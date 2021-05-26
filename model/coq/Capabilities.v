(* Coq formalization on CHERI Capablities *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Constructive_sets.

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
  Local Notation "x <= y" := (V_lt x y \/ x=y).

  Inductive Interval : Type :=
  | Incl_Interval (base top:V): (base <= top) -> Interval (* inclusive *)
  | Empty_Interval (base:V): Interval. (* empty with base *)

  (* [<=] relation on intervals *)
  Definition interval_leq: relation (Interval) :=
    fun i1 i2 =>
      match i1, i2 with
      | Empty_Interval b1, Empty_Interval b2 => b1 = b2
      | @Incl_Interval b1 t1 _, @Incl_Interval b2 t2 _ =>  b2 <= b1 /\ t1 <= t2
      | Empty_Interval b1, @Incl_Interval b2 t2 _ =>  b2 <= b1 /\ b1 <= t2
      | @Incl_Interval b1 t1 _, Empty_Interval b2 =>  False
      end.

End Interval.
Arguments Incl_Interval {V}%type_scope {V_lt}%type_scope.
Arguments Empty_Interval {V}%type_scope {V_lt}%type_scope.

Class CAddress (A:Type) :=
  {
  (* "less than" *)
  address_lt: relation A;
  address_lt_irref: forall a, ~ address_lt a a;

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

(*
Section PermissinProperties.
  Context `{ADR: CAddress A}.

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
 *)

Class CObjectType (OT:Type)
  :=
    {
    }.

Section CapabilityDefinition.

  Context `{OTYPE: @CObjectType OT}
          `{ADR: CAddress}.

  Variant CapSeal :=
  | Cap_Unsealed
  | Cap_SEntry
  | Cap_Indirect_SEntry
  | Cap_Sealed (otype:OT).

  (* Abstract generic capability. *)
  Class CCapability (C:Type) :=
    {
    (* Formerly "is_tagged" *)
    is_valid: C -> Prop;

    (* Get informaiton about "seal" on this capability *)
    get_seal: C -> CapSeal;

    (* TODO: these are for setting "simple" sealing.
       Do we need similar for sentry and indirect sentry ? *)
    seal: C -> OT -> C;
    unseal: C -> C;

    is_global: C -> Prop;
    clear_global: C -> C;

    (* Some additional logical properties from Isabelle Capabilities "locale" *)

    is_valid_seal: forall c t, is_valid (seal c t) = is_valid c ;

    is_valid_unseal: forall c, is_valid (unseal c) = is_valid c ;

    is_valid_clear_global: forall c, is_valid (clear_global c) = is_valid c ;

    }.

  (* Capability associated with memory address *)
  Class CSealingCapability (C:Type) :=
    {
    sealing_ccapbility :> CCapability(C);

    (* Sealin permissions. TODO: exclusive *)
    permits_seal: C -> Prop;
    permits_unseal: C -> Prop;
    }.

  (* Capability for "integer type tokens" *)
  Class CTokenCapability (C:Type) :=
    {
    token_ccapbility :> CCapability(C);

    (* Previously "get_cursor" *)
    get_value: C -> OT;
    }.

  (* Capability associated with memory address *)
  Class CMemoryCapability (C:Type) :=
    {
    memory_ccapbility :> CCapability(C);

    (* Memory-related permissions: TODO: at least one must be set *)
    permits_execute: C -> Prop;
    permits_ccall: C -> Prop;
    permits_load: C -> Prop;
    permits_load_cap: C -> Prop;
    permits_store: C -> Prop;
    permits_store_cap: C -> Prop;
    permits_store_local_cap: C -> Prop;
    permits_system_access: C -> Prop;

    (* Previously "get_cursor" *)
    get_address: C -> A;

    (* Returns either inclusive bounds for covered
     memory region *)
    get_bounds: C -> address_interval;

    (* Capabilities Bounds Invariants *)

    bounds_seal_eq: forall c otype, get_bounds (seal c otype) = get_bounds c ;

    bounds_clear_global_eq: forall c, get_bounds (clear_global c) = get_bounds c;
    }.

End CapabilityDefinition.

Section CCapabilityProperties.

  Context `{OTYPE: @CObjectType OT}
          `{ADR: CAddress A}
          `{CAPA: @CCapability OT C}.

  (* Helper function to check if capability is sealed (with any kind of seal) *)
  Definition is_sealed (c:C) : Prop
    := match get_seal c with
       | Cap_Unsealed => False
       | _ => True
       end.

  (* Helper function to check if sealed entry capability *)
  Definition is_sentry (c:C) : Prop
    := match get_seal c with
       | Cap_SEntry => True
       | _ => False
       end.

  (* Helper function to check if indirect entry capability *)
  Definition is_indirect_sentry (c:C) : Prop
    := match get_seal c with
       | Cap_Indirect_SEntry => True
       | _ => False
       end.

  (* Return [None] it the capability is "unsealed" and
     [Some OT] otherwise *)
  Definition get_obj_type (c:C): option OT
    := match get_seal c with
       | Cap_Sealed otype => Some otype
       | _ => None
       end.

  (* Set of cap type alias *)
  Definition cap_set := Ensemble C.

  Definition cat_set_in (x:C) (cs:cap_set) : Prop
    := In _ cs x.

  Section CMemoryCapabilityProperties.
    Context `{CM: @CMemoryCapability OT A ADR C}.

    Definition get_mem_region (c:C): address_set
      := addresses_in_interval (get_bounds c).

    (* "<=" relation on bounds *)
    Definition bounds_leq: relation C :=
      fun c1 c2 => interval_leq (get_bounds c1) (get_bounds c2).

  End CMemoryCapabilityProperties.

  (* "<=" relation on Capabilities *)
  Definition cap_leq: relation C :=
    fun c1 c2 =>
      c1 = c2
      \/ ~ is_valid c1
      \/ (is_valid c2
         /\ ~ is_sealed c1 /\ ~ is_sealed c2
         /\ bounds_leq c1 c2
         /\ (is_global c1 -> is_global c2)
         /\ perms_leq (get_perms c1) (get_perms c2)).

  Local Notation "x <= y" := (cap_leq x y).
  Definition invokable (cc cd: C): Prop:=
    let pc := get_perms cc in
    let pd := get_perms cd in
    is_valid cc /\ is_valid cd /\
    is_sealed cc /\ is_sealed cd /\
    ~ is_sentry cc /\ ~ is_sentry cd /\
    permits_ccall pc /\ permits_ccall pd /\
    get_obj_type cc = get_obj_type cd /\
    permits_execute pc /\ ~ permits_execute pd.

  Definition pred_clear_global_unless (g:Prop) (c1 c2:C) (pred: C -> C -> Prop): Prop:=
    (g /\ pred c1 c2) \/
    (~g /\ pred (clear_global c1) c2).

  Inductive derivable (cs:cap_set) : Ensemble C :=
  | Copy: forall c, cat_set_in c cs -> derivable cs c
  | Restrict: forall c c', derivable cs c'  -> c <= c' -> derivable cs c
  | Unseal_global:
      forall c' c'',
        derivable cs c' ->
        derivable cs c'' ->
        is_valid c' ->
        is_valid c'' ->
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
        is_valid c' ->
        is_valid c'' ->
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
        is_valid c' ->
        is_valid c'' ->
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
        is_valid c' ->
        ~ is_sealed c' ->
        (is_sentry (seal c' otype) \/
         is_indirect_sentry (seal c' otype))
        ->
        derivable cs (seal c' otype).

  Local Notation "x ⊆ y" := (Included _ x y) (at level 61, right associativity).
  Local Notation "x ∪ y" := (Union _ x y) (at level 61, right associativity).
  Local Notation "x ∩ y" := (Intersection _ x y) (at level 61, right associativity).

  (* "Monotonicity" property *)
  Lemma derivable_mono:
    forall cs cs', cs ⊆ cs' -> derivable cs ⊆ derivable cs'.
  Proof.
    intros cs cs' H c IN.
    induction IN.
    -
      apply Copy.
      apply H, H0.
    - eapply Restrict; eauto.
    - eapply Unseal_global; eauto.
    - eapply Unseal_not_global; eauto.
    - eapply Seal; eauto.
    - eapply SealEntry; eauto.
  Qed.

  (* "Extensive" property (as in closure operators).
     Formely known as "derivable_refl".
   *)
  Lemma derivable_extensive:
    forall cs, cs ⊆ derivable cs.
  Proof.
    intros cs c H.
    constructor 1.
    apply H.
  Qed.

  (* idempotentence property *)
  Lemma derivable_idemp:
    forall cs, derivable (derivable cs) = derivable cs.
  Proof.
    intros cs.
    apply Extensionality_Ensembles.
    split.
    -
      intros x H.
      induction H; unfold cat_set_in, In in *.
      + auto.
      + eapply Restrict; eauto.
      + eapply Unseal_global; eauto.
      + eapply Unseal_not_global; eauto.
      + eapply Seal; eauto.
      + eapply SealEntry; eauto.
    -
      intros x H.
      induction H; unfold cat_set_in, In in *.
      + apply Copy; apply Copy; auto.
      + eapply Restrict; eauto.
      + eapply Unseal_global; eauto.
      + eapply Unseal_not_global; eauto.
      + eapply Seal; eauto.
      + eapply SealEntry; eauto.
  Qed.

  Lemma derivable_empty: derivable empty_address_set = empty_address_set.
  Proof.
    unfold empty_address_set.
    apply Extensionality_Ensembles.
    unfold Same_set, Included.
    split; intros.
    -
      unfold In in H.
      induction H.
      + apply Noone_in_empty in H; tauto.
      + apply Noone_in_empty in IHderivable; tauto.
      + apply Noone_in_empty in IHderivable1; tauto.
      + apply Noone_in_empty in IHderivable1; tauto.
      + apply Noone_in_empty in IHderivable1; tauto.
      + apply Noone_in_empty in IHderivable; tauto.
    -
      apply Noone_in_empty in H; tauto.
  Qed.

  Lemma derivable_union_subseteq_absorb:
    forall cs cs',
      cs' ⊆ derivable cs ->
      derivable (cs ∪ cs') = derivable cs.
  Proof.
    intros cs cs' H.
    apply Extensionality_Ensembles.
    split.
    -
      intros c H0.
      induction H0.
      +
        apply Union_inv in H0.
        destruct H0.
        *
          apply Copy, H0.
        *
          specialize (H c).
          apply H, H0.
      + eapply Restrict; eauto.
      + eapply Unseal_global; eauto.
      + eapply Unseal_not_global; eauto.
      + eapply Seal; eauto.
      + eapply SealEntry; eauto.
    -
      apply derivable_mono.
      intros x H0.
      apply Union_introl.
      auto.
  Qed.

  (* Formely known as "derivable_Int1_subset" *)
  Lemma derivable_IntL_subset:
    forall a b, derivable (a ∩ b) ⊆ derivable a.
  Proof.
    intros a b.
    apply derivable_mono.
    unfold Included.
    intros c H.
    apply Intersection_inv in H.
    apply H.
  Qed.

  (* Formely known as "derivable_Int2_subset" *)
  Lemma derivable_IntR_subset:
    forall a b, derivable (a ∩ b) ⊆ derivable b.
  Proof.
    intros a b.
    apply derivable_mono.
    unfold Included.
    intros c H.
    apply Intersection_inv in H.
    apply H.
  Qed.

End CCapabilityProperties.
