(* Coq formalization on CHERI Capablities *)

Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Relations.Relation_Definitions.

Require Import bbv.Word.

Set Implicit Arguments.
Set Strict Implicit.
Generalizable All Variables.

Import ListNotations.
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

(* Various architeture-dependent definitions affecting CHERI *)
Class CArch (A:Type) :=
  {
  (* Number of bits for permissions *)
  perms_nbits: nat ;

  (* Number of bits describing object type.
     TODO: maybe use max value instead?
   *)
  otype_nbits: nat;

  (* Size of capability encoding in bytes *)
  capability_nbyes: nat;

  (* Type to describe memory byte *)
  memory_byte:Type;
  }.

Class CAddress (A:Type) :=
  {
  (* "less than" *)
  address_lt: relation A;
  address_lt_irref: forall a, ~ address_lt a a;

  address_eq_dec: forall a b : A, {a = b} + {a <> b};
  address_lt_dec: forall a b : A, {address_lt a b}+{~ address_lt a b};

  (* Generates of set of addresses in the given range. *)
  addresses_in_interval: (Interval address_lt)-> {l:list A| NoDup l} ;
  }.

Section CAddressProperties.
  Context `{ADR: CAddress A}.

  (* address interval. *)
  Definition address_interval := Interval address_lt.

  (* Set of addresses type alias *)
  Definition address_set := {l:list A| NoDup l} .

  (* Set membership predicate *)
  Definition address_set_in (a:A) (xs:address_set) : Prop
    := List.In a (proj1_sig xs).

  (* Empty address set constant *)
  Definition empty_address_set: address_set := @exist _ _ [] (NoDup_nil _).

  (* "less of equal" relation on on addresses *)
  Definition address_le: relation A :=
    fun a b => address_lt a b \/ a = b.

End CAddressProperties.

Class CPermission (P:Type)
      `{ARCH: CArch A}:=
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

  (* Encode permissions as a bit vector *)
  perms_encode: P -> word (perms_nbits)
  }.

Section PermissinProperties.
  Context `{ARCH: CArch A}
          `{ADR: CAddress Address}
          `{PERM: @CPermission P A ARCH}.

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
      `{ARCH: CArch A} :=
  {
  (* Decidable equality *)
  ot_eq_dec: forall a b : OT, {a = b} + {a <> b};

  (* encode object type as bit vector *)
  ot_encode: OT -> word (otype_nbits);
  }.

Class CCapability (C:Type)
      `{ARCH: CArch AR}
      `{OTYPE: @CObjectType OT AR ARCH}
      `{ADR: CAddress A}
      `{PERM: @CPermission P AR ARCH} :=
  {

  (* Decidable equality *)
  cap_eq_dec: forall a b : C, {a = b} + {a <> b};

  is_tagged: C -> Prop;
  is_sentry: C -> Prop;
  is_indirect_sentry: C -> Prop;

  (* Returns either inclusive bounds for covered
     memory region *)
  get_bounds: C -> address_interval;

  (* Return [None] it the capability is "unsealed" and
     [Some OT] otherwise *)
  get_obj_type: C -> option OT;
  get_perms: C -> P;
  get_address: C -> A;

  seal: C -> OT -> C;
  unseal: C -> C;

  is_global: C -> Prop;
  clear_global: C -> C;

  (* Partial mapping between addresses and object types.
     TODO: Maybe should be moved elswhwere, like [CArch].
   *)
  otype_of_address: A -> option OT;

  (* Try to decode sequence of bytes as a capability *)
  cap_decode: (Vector.t memory_byte capability_nbyes) -> bool -> option C;
  }.

Section CCapabilityProperties.

  Context `{ARCH: CArch AR}
          `{OTYPE: @CObjectType OT AR ARCH}
          `{ADR: CAddress A}
          `{PERM: @CPermission P AR ARCH}
          `{CAPA: @CCapability C AR ARCH OT OTYPE A ADR P PERM}.


  (* Set of cap type alias *)
  Definition cap_set := {l:list C| NoDup l} .

  Definition cat_set_in (x:C) (cs:cap_set) : Prop
    := List.In x (proj1_sig cs).

  Definition is_sealed (c:C) : Prop
    := match get_obj_type c with
       | None => False
       | Some _ => True
       end.

  Definition get_mem_region (c:C): address_set
    := addresses_in_interval (get_bounds c).

  (* "<=" relation on bounds *)
  Definition leq_bounds: relation C :=
    fun c1 c2 => interval_leq (get_bounds c1) (get_bounds c2).

  (* "<=" relation on Capabilities *)
  Definition leq_cap: relation C :=
    fun c1 c2 =>
      c1 = c2
      \/ (~ is_tagged c1)
      \/ (is_tagged c2 /\
         (~ is_sealed c1 /\ ~ is_sealed c2) /\
         (leq_bounds c1 c2) /\
         (is_global c1 -> is_global c2) /\
         (perms_leq (get_perms c1) (get_perms c2))).

  Definition invokable (cc cd: C): Prop:=
    let pc := get_perms cc in
    let pd := get_perms cd in
    is_tagged cc /\ is_tagged cd /\
    is_sealed cc /\ is_sealed cd /\
    ~ is_sentry cc /\ ~ is_sentry cd /\
    permits_ccall pc /\ permits_ccall pd /\
    get_obj_type cc = get_obj_type cd /\
    permits_execute pc /\ ~ permits_execute pd.

  Definition eq_clear_global_unless (g:Prop) (c1 c2:C): Prop:=
    (g /\ c1 = c2) \/
    (~g /\ clear_global c1 = c2).

  (* Derivation of capabilities, bounded by derivation depth to
     guarantee termination *)
  Fixpoint cap_derivable_bounded (n:nat) (cs:cap_set) (c:C): Prop :=
    match n with
    | O => cat_set_in c cs
    | S n =>
      (exists c', cap_derivable_bounded n cs c' /\ leq_cap c c') \/
      (exists c' otype, cap_derivable_bounded n cs c'
                   /\ is_tagged c'
                   /\ ~ is_sealed c'
                   /\ seal c' otype = c
                   /\ (is_sentry c \/ is_indirect_sentry c)) \/
      (exists c' c'',
          cap_derivable_bounded n cs c'
          /\ cap_derivable_bounded n cs c''
          /\ is_tagged c'
          /\ is_tagged c''
          /\ not (is_sealed c'')
          /\ address_set_in (get_address c'') (get_mem_region c'')
          /\ (exists ot'',
                (otype_of_address (get_address c'') = Some ot'') /\
                ((is_sealed c'
                  /\ permits_unseal (get_perms c'')
                  /\ get_obj_type c' = Some ot''
                  /\ eq_clear_global_unless (is_global c'') (unseal c') c
                 )  \/
                 (~ is_sealed c'
                  /\ permits_seal (get_perms c'')
                  /\ seal c' ot'' = c))
            )
      )
    end.

End CCapabilityProperties.
