(* Coq formalization on CHERI Capablities based on
   `capablities.lem` *)

Require Import Coq.Lists.List.
(* Require Import bbv.Word. *)
From Coq.FSets Require Import
     FSetAVL
     FSetInterface
     FSetFacts
     FSetProperties
     FSetToFiniteSet.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope nat_scope.
Open Scope list_scope.

(* Set of natural numbers *)
Module NS := FSetAVL.Make(Nat_as_OT).
Module Import NSP := FSetProperties.WProperties_fun(Nat_as_OT)(NS).
Module Import NE := FSetToFiniteSet.WS_to_Finite_set(Nat_as_OT)(NS).

Definition perms   := list bool.
Definition address := nat.
Definition otype   := nat.

Definition address_set := NS.t.

(* From `sail2_values.lem` *)
Inductive bitU := B0 | B1 | BU.

(* From `sail2_values.lem` *)
Definition memory_byte := list bitU.

Class Capability (C:Type) :=
  {
  is_tagged : C -> bool;
  is_sealed : C -> bool;
  is_sentry : C -> bool;
  is_indirect_sentry : C -> bool;
  get_base : C -> address;
  get_top : C -> address;
  get_obj_type : C -> otype;
  get_perms : C -> perms;
  get_cursor : C -> address;
  is_global : C -> bool;
  seal : C -> otype -> C;
  unseal : C -> C;
  clear_global : C -> C;
  cap_of_mem_bytes : list memory_byte -> bitU -> option C;
  permits_execute : C -> bool;
  permits_ccall : C -> bool;
  permits_load : C -> bool;
  permits_load_cap : C -> bool;
  permits_seal : C -> bool;
  permits_store : C -> bool;
  permits_store_cap : C -> bool;
  permits_store_local_cap : C -> bool;
  permits_system_access : C -> bool;
  permits_unseal : C -> bool;
  }.

Definition address_range (start:address) (len:address): list address
  := List.map (fun n => start +n) (List.seq 0 len).


Definition get_mem_region {C:Type} `{Capability C} (c:C): address_set
  :=
    if get_top c <? get_base c then NS.empty else
      let len := get_top c - get_base c in
      NSP.of_list (address_range (get_base c) len).

Fixpoint leq_bools (l1 l2: list bool): bool
  :=
    match (l1, l2) with
    | ([], []) => true
    | (_::_, []) => false
    | ([], _::_) => false
    | (b1 :: l1, b2 :: l2) => (implb b1 b2) && leq_bools l1 l2
    end.

Definition leq_perms: perms -> perms -> bool:= leq_bools.

Definition leq_bounds {C:Type} `{Capability C} (c1 c2:C): bool
  :=
    ((get_base c1 =? get_base c2) && (get_top c1 =? get_top c2))
    || ((get_base c2 <=? get_base c1)
       && (get_top c1 <=? get_top c2)
       && (get_base c1 <=? get_top c1)).
