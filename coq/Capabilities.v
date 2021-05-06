(* Coq formalization on CHERI Capablities based on
   `capablities.lem` *)

Require Import bbv.Word.

Definition perms   := list bool.
Definition address := nat.
Definition otype   := nat.

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
