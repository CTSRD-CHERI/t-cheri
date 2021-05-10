(* Coq formalization on CHERI Capablities based on
   `capablities.lem` *)

Require Import Coq.Lists.List.
(* Require Import bbv.Word. *)
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope nat_scope.
Open Scope list_scope.

(* TODO: size by arch *)
Definition perms   := list bool.

(* TODO: abstract *)
Definition address := nat.

(* TODO: Bitvector with size defined by arch *)
Definition otype   := nat.

Section AddressSet.

  Definition address_set := {l:list address| NoDup l}.

  Definition empty_address_set:address_set := @exist _ _ [] (NoDup_nil _).

End AddressSet.

(* TODO: abstract *)
Parameter memory_byte:Type.

Class Permission (P:Type) :=
  {
  (* Convenience functions to examine some permission bits *)
  permits_execute : P -> bool;
  permits_ccall : P -> bool;
  permits_load : P -> bool;
  permits_load_cap : P -> bool;
  permits_seal : P -> bool;
  permits_store : P -> bool;
  permits_store_cap : P -> bool;
  permits_store_local_cap : P -> bool;
  permits_system_access : P -> bool;
  permits_unseal : P -> bool;

  (* Get all permission bits *)
  get_bits : P -> perms;
  }.

Class Capability (C P:Type) `{Permission P} :=
  {
  is_tagged : C -> bool;
  is_sealed : C -> bool;
  is_sentry : C -> bool;
  is_indirect_sentry : C -> bool;
  get_base : C -> address;
  get_top : C -> address;
  get_obj_type : C -> otype;
  get_perms : P -> perms;
  get_cursor : C -> address;
  is_global : C -> bool;
  seal : C -> otype -> C;
  unseal : C -> C;
  clear_global : C -> C;
  (* TODO: size of memory block should be in arch *)
  cap_of_mem_bytes : list memory_byte -> bool -> option C;
  }.

Definition address_range (start:address) (len:address): list address
  := List.map (fun n => start +n) (List.seq 0 len).

Definition get_mem_region {C:Type} `{Capability C} (c:C): address_set
  :=
    if get_top c <? get_base c then empty_address_set else
      let len := get_top c - get_base c in
      (address_range (get_base c) len).

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
