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
Open Scope bool_scope.

(* Various architeture-dependent definitions affecting CHERI *)
Class Arch (A:Type) :=
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

Class Address (A:Type) :=
  {
  (* "less than" *)
  address_lt: relation A;
  address_lt_irref: forall a, ~ address_lt a a;

  address_eq_dec: forall a b : A, {a = b} + {a <> b};
  address_lt_dec: forall a b : A, {address_lt a b}+{~ address_lt a b};

  (* Generates of set of addresses in the given range. *)
  addresses_in_interval: (Interval address_lt)-> {l:list A| NoDup l} ;
  }.

Section AddressHelpers.
  Context `{ADR: Address A}.

  (* address interval. *)
  Definition address_interval := Interval address_lt.

  (* Set of addresses type aliase *)
  Definition address_set := {l:list A| NoDup l} .

  (* Empty address set constant *)
  Definition empty_address_set: address_set := @exist _ _ [] (NoDup_nil _).

  (* boolean versoin of [=] *)
  Definition address_eqb: A -> A -> bool :=
    fun a b => if address_eq_dec a b then true else false.

  (* boolean versoin of [address_lt] preficate *)
  Definition address_ltb: A -> A -> bool :=
    fun a b => if address_lt_dec a b then true else false.

  (* boolean "less of equal" perdicate on on addresses *)
  Definition address_leb: A -> A -> bool :=
    fun a b => address_ltb a b || address_eqb a b.

End AddressHelpers.

Class Permission (P:Type)
      `{ARCH: Arch A}:=
  {
  (* Convenience functions to examine some permission bits *)
  permits_execute: P -> bool;
  permits_ccall: P -> bool;
  permits_load: P -> bool;
  permits_load_cap: P -> bool;
  permits_seal: P -> bool;
  permits_store: P -> bool;
  permits_store_cap: P -> bool;
  permits_store_local_cap: P -> bool;
  permits_system_access: P -> bool;
  permits_unseal: P -> bool;

  (* Get all permission bits *)
  get_bits: P -> word (perms_nbits)
  }.

Class Capability (C:Type)
      `{ARCH: Arch A}
      `{ADR: Address address}
      `{PERM: @Permission P A ARCH} :=
  {

  is_tagged: C -> bool;
  is_sealed: C -> bool;
  is_sentry: C -> bool;
  is_indirect_sentry: C -> bool;

  (* Returns either inclusive bounds for covered
     memory region *)
  get_bounds: C -> address_interval;

  get_obj_type: C -> word (otype_nbits);
  get_perms: C -> P;
  get_cursor: C -> address;

  seal: C -> word (otype_nbits) -> C;
  unseal: C -> C;

  is_global: C -> bool;
  clear_global: C -> C;

  cap_of_mem_bytes: (Vector.t memory_byte capability_nbyes) -> bool -> option C;
  }.

Section CapabilityProperties.

  Context `{ARCH: Arch A}
          `{ADR: Address address}
          `{PERM: @Permission P A ARCH}
          `{CAPA: @Capability C A ARCH  address ADR P PERM}.

  Definition get_mem_region (c:C): address_set
    := addresses_in_interval (get_bounds c).

  Definition leq_bounds (c1 c2:C): bool :=
    if interval_leq_dec
         address_lt_irref
         address_eq_dec
         address_lt_dec
         (get_bounds c1) (get_bounds c2)
    then true else false.

End CapabilityProperties.
