(* Coq formalization on CHERI Capablities *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.

Set Implicit Arguments.
Set Strict Implicit.
Generalizable All Variables.

Open Scope nat_scope.
Open Scope list_scope.

Section Interval.
  Variable V:Type.
  Variable V_lt: V -> V -> Prop.
  Variable V_lt_irref: forall a, ~ V_lt a a.

  Local Notation "x < y"  := (V_lt x y).
  Local Notation "x <= y" := (V_lt x y /\ x=y).

  Inductive Interval :=
  | Incl_Interval (base top:V): (base=top /\ base < top) -> Interval
  | Empty_Interval (base:V): Interval.

  (* [<=] relation on intervals *)
  Definition interval_leq: relation (Interval) :=
    fun i1 i2 =>
      match i1, i2 with
      | Empty_Interval b1, Empty_Interval b2 => b1 = b2
      | @Incl_Interval b1 t1 _, @Incl_Interval b2 t2 _ =>  b2 <= b1 /\ t1 <= t2
      | Empty_Interval b1, @Incl_Interval b2 t2 _ =>  b2 <= b1 /\ b1 <= t2
      | @Incl_Interval b1 t1 _, Empty_Interval b2 =>  False
      end.

  Fact interval_leq_dec:
    (forall x y : V, {x = y} + {x <> y}) ->
    (forall x y, {V_lt x y}+{~ V_lt x y}) ->
    forall a b, {interval_leq a b}+{~ interval_leq a b}.
  Proof.
    intros EQDEC LTDEC a b.
    destruct a as [b1 t1 [b1t1e b1t1l] | b1], b as [b2 t2 [b2t2e b2t2l] | b2]; subst;cbn;auto.
    -
      apply V_lt_irref in b1t1l.
      tauto.
    -
      apply V_lt_irref in b2t2l.
      tauto.
  Qed.

End Interval.
Arguments Incl_Interval {V}%type_scope {V_lt}%type_scope.
Arguments Empty_Interval {V}%type_scope {V_lt}%type_scope.

Class CAddress (A:Type) :=
  {
  (* "less than" *)
  address_lt: relation A;
  address_lt_irref: forall a, ~ address_lt a a;

  address_eq_dec: forall a b : A, {a = b} + {a <> b};
  address_lt_dec: forall a b : A, {address_lt a b}+{~ address_lt a b};

  (* Generates of set of addresses in the given range. *)
  addresses_in_interval: (Interval address_lt) -> Ensemble A;
  }.

Section CAddressProperties.
  Context `{ADR: CAddress A}.

  (* address interval. *)
  Definition address_interval := Interval address_lt.

  (* Set of addresses type alias *)
  Definition address_set := Ensemble A.

  (* Set membership predicate *)
  Definition address_set_in (a:A) (xs:address_set) : Prop
    := In _ xs a.

  (* Empty address set constant *)
  Definition empty_address_set: address_set := Empty_set A.

  (* "less of equal" relation on on addresses *)
  Definition address_le: relation A :=
    fun a b => address_lt a b \/ a = b.

End CAddressProperties.

Class CPermission (P:Type) :=
  {
  (* Convenience functions to examine some permission bits *)
  permits_execute: P -> Prop;
  permits_ccall: P -> Prop;
  permits_load: P -> Prop;
  permits_load_cap: P -> Prop;
  permits_seal: P -> Prop;
  permits_store: P -> Prop;
  permits_store_cap: P -> Prop;
  permits_store_local_cap: P -> Prop;
  permits_system_access: P -> Prop;
  permits_unseal: P -> Prop;
  }.

Section PermissinProperties.
  Context `{ADR: CAddress A}
          `{PERM: @CPermission P}.

  (* Logical comparison ofpermssions based solely on their properties
     expressed in [Permissoin] typeclass interface.  Underlying
     implementation type may have some additional fields not
     considered here *)
  Definition perms_eq (p1 p2: P): Prop :=
    (permits_execute p1         ) = (permits_execute p2) /\
    (permits_ccall p1           ) = (permits_ccall p2) /\
    (permits_load p1            ) = (permits_load p2) /\
    (permits_load p1            ) = (permits_load p2) /\
    (permits_seal p1            ) = (permits_seal p2) /\
    (permits_store p1           ) = (permits_store p2) /\
    (permits_store_cap p1       ) = (permits_store_cap p2) /\
    (permits_store_local_cap p1 ) = (permits_store_local_cap p2) /\
    (permits_system_access p1   ) = (permits_system_access p2) /\
    (permits_unseal p1          ) = (permits_unseal p2).

  (* Logical "lessn than" comparison of permssions based solely on
     their properties expressed in [Permissoin] typeclass
     interface.  Underlying implementation type may have some
     additional fields not considered here *)
  Definition perms_leq (p1 p2: P): Prop :=
    ((permits_execute p1         ) -> (permits_execute p2)) /\
    ((permits_ccall p1           ) -> (permits_ccall p2)) /\
    ((permits_load p1            ) -> (permits_load p2)) /\
    ((permits_load p1            ) -> (permits_load p2)) /\
    ((permits_seal p1            ) -> (permits_seal p2)) /\
    ((permits_store p1           ) -> (permits_store p2)) /\
    ((permits_store_cap p1       ) -> (permits_store_cap p2)) /\
    ((permits_store_local_cap p1 ) -> (permits_store_local_cap p2)) /\
    ((permits_system_access p1   ) -> (permits_system_access p2)) /\
    ((permits_unseal p1          ) -> (permits_unseal p2)).

End PermissinProperties.

Class CObjectType (OT:Type)
  :=
    {
  (* Decidable equality *)
  ot_eq_dec: forall a b : OT, {a = b} + {a <> b};
    }.


Section CapabilityDefinition.
  Context `{OTYPE: @CObjectType OT}
          `{ADR: CAddress}
          `{PERM: @CPermission P}.

  (* Various types of seals supported *)
  Variant CapSealType :=
  | Cap_Seal
  | Cap_SEntry
  | Cap_Indirect_SEntry.

  Variant CapSeal :=
  | Cap_Unsealed
  | Cap_Sealed (sealtype:CapSealType) (otype:OT).

  Class CCapability (C:Type) :=
    {

    (* Decidable equality *)
    cap_eq_dec: forall a b : C, {a = b} + {a <> b};

    (* TODO: "is_valid" is perhaps more friendly name ? *)
    is_tagged: C -> Prop;

    (* Returns either inclusive bounds for covered
     memory region *)
    get_bounds: C -> address_interval;

    get_perms: C -> P;

    (* Previously "get_cursor" *)
    get_address: C -> A;

    (* Get informaiton about "seal" on this capability *)
    get_seal: C -> CapSeal;

    (* TODO: these are for setting "simple" sealing.
       Do we need similar for sentry and indirect sentry ? *)
    seal: C -> OT -> C;
    unseal: C -> C;

    is_global: C -> Prop;
    clear_global: C -> C;

    otype_of_address: A -> option OT;

    (* Some additional logical properties from Isabelle "locale" *)

    is_tagged_seal: forall c t, is_tagged (seal c t) = is_tagged c ;

    is_tagged_unseal: forall c, is_tagged (unseal c) = is_tagged c ;

    is_tagged_clear_global: forall c, is_tagged (clear_global c) = is_tagged c ;

    }.

End CapabilityDefinition.

Section CCapabilityProperties.

  Context `{OTYPE: @CObjectType OT}
          `{ADR: CAddress A}
          `{PERM: @CPermission P}
          `{CAPA: @CCapability OT A ADR P C}.

  (* Helper function to check if capability is sealed (with any kind of seal *)
  Definition is_sealed (c:C) : Prop
    := match get_seal c with
       | Cap_Sealed _ _ => True
       | _ => False
       end.

  (* Helper function to check if sealed entry capability *)
  Definition is_sentry (c:C) : Prop
    := match get_seal c with
       | Cap_Sealed Cap_SEntry _ => True
       | _ => False
       end.

  (* Helper function to check if indirect entry capability *)
  Definition is_indirect_sentry (c:C) : Prop
    := match get_seal c with
       | Cap_Sealed Cap_Indirect_SEntry _ => True
       | _ => False
       end.
  (* Return [None] it the capability is "unsealed" and
     [Some OT] otherwise *)
  Definition get_obj_type (c:C): option OT
    := match get_seal c with
       | Cap_Sealed _ otype => Some otype
       | _ => None
       end.

  (* Set of cap type alias *)
  Definition cap_set := Ensemble C.

  Definition cat_set_in (x:C) (cs:cap_set) : Prop
    := In _ cs x.

  Definition get_mem_region (c:C): address_set
    := addresses_in_interval (get_bounds c).

  (* "<=" relation on bounds *)
  Definition bounds_leq: relation C :=
    fun c1 c2 => interval_leq (get_bounds c1) (get_bounds c2).

  (* "<=" relation on Capabilities *)
  Definition cap_leq: relation C :=
    fun c1 c2 =>
      c1 = c2
      \/ ~ is_tagged c1
      \/ (is_tagged c2
         /\ ~ is_sealed c1 /\ ~ is_sealed c2
         /\ bounds_leq c1 c2
         /\ (is_global c1 -> is_global c2)
         /\ perms_leq (get_perms c1) (get_perms c2)).

  Local Notation "x ⊆ y" := (cap_leq x y) (at level 60, right associativity).

  Definition invokable (cc cd: C): Prop:=
    let pc := get_perms cc in
    let pd := get_perms cd in
    is_tagged cc /\ is_tagged cd /\
    is_sealed cc /\ is_sealed cd /\
    ~ is_sentry cc /\ ~ is_sentry cd /\
    permits_ccall pc /\ permits_ccall pd /\
    get_obj_type cc = get_obj_type cd /\
    permits_execute pc /\ ~ permits_execute pd.

  Definition pred_clear_global_unless (g:Prop) (c1 c2:C) (pred: C -> C -> Prop): Prop:=
    (g /\ pred c1 c2) \/
    (~g /\ pred (clear_global c1) c2).

  Inductive derivable (cs:cap_set) : C ->  Prop :=
  | Copy: forall c, cat_set_in c cs -> derivable cs c
  | Restrict: forall c c', derivable cs c'  -> c ⊆ c' -> derivable cs c
  | Unseal_global:
      forall c' c'',
        derivable cs c' ->
        derivable cs c'' ->
        is_tagged c' ->
        is_tagged c'' ->
        ~ is_sealed c'' ->
        is_sealed c' ->
        permits_unseal (get_perms c'') ->
        get_obj_type c' = otype_of_address (get_address c'') ->
        address_set_in (get_address c'') (get_mem_region c'') ->
        is_global c''
        ->
        derivable cs (unseal c')
  | Unseal_not_global:
      forall c' c'',
        derivable cs c' ->
        derivable cs c'' ->
        is_tagged c' ->
        is_tagged c'' ->
        ~ is_sealed c'' ->
        is_sealed c' ->
        permits_unseal (get_perms c'') ->
        get_obj_type c' = otype_of_address (get_address c'') ->
        address_set_in (get_address c'') (get_mem_region c'') ->
        ~ is_global c''
        ->
        derivable cs (clear_global (unseal c'))
  | Seal:
      forall c' c'' ot'', (* TODO: not sure about quantification on ot'' *)
        derivable cs c' ->
        derivable cs c'' ->
        is_tagged c' ->
        is_tagged c'' ->
        ~ is_sealed c' ->
        ~ is_sealed c'' ->
        permits_seal (get_perms c'') ->
        address_set_in (get_address c'') (get_mem_region c'')  ->
        otype_of_address (get_address c'') = Some ot''
        ->
        derivable cs (seal c' ot'')
  | SealEntry:
      forall c' otype,
        derivable cs c' ->
        is_tagged c' ->
        ~ is_sealed c' ->
        (is_sentry (seal c' otype) \/
         is_indirect_sentry (seal c' otype))
        ->
        derivable cs (seal c' otype).

End CCapabilityProperties.
