(* Coq formalization on CHERI Capablities *)

Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Require Import Coq.Arith.PeanoNat.

Require Import bbv.Word.

Set Implicit Arguments.
Set Strict Implicit.

Import ListNotations.
Open Scope nat_scope.
Open Scope list_scope.

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

(* TODO: abstract *)
Definition address := nat.

Section AddressSet.

  Definition address_set := {l:list address| NoDup l}.

  Definition empty_address_set:address_set := @exist _ _ [] (NoDup_nil _).

End AddressSet.

Class Permission (P:Type)
      {A:Type} `{Arch A}:=
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
  get_bits : P -> word (perms_nbits)
  }.

Class Capability (C:Type)
      {A:Type} `{AA:Arch A}
      {P:Type} `{@Permission P A AA} :=
  {
  is_tagged : C -> bool;
  is_sealed : C -> bool;
  is_sentry : C -> bool;
  is_indirect_sentry : C -> bool;
  get_base : C -> address;
  get_top : C -> address;
  get_obj_type : C -> word (otype_nbits);
  get_perms : C -> P;
  get_cursor : C -> address;
  is_global : C -> bool;
  seal : C -> word (otype_nbits) -> C;
  unseal : C -> C;
  clear_global : C -> C;
  cap_of_mem_bytes : (Vector.t memory_byte capability_nbyes) -> bool -> option C;
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
