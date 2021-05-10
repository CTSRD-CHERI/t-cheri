(* Coq formalization on CHERI Capablities *)

Require Import Coq.Lists.List.
Require Import Coq.Vectors.Vector.
Require Import Coq.Arith.PeanoNat.

Require Import bbv.Word.

Set Implicit Arguments.
Set Strict Implicit.
Generalizable All Variables.

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

Class Address (A:Type) :=
  {

  (* "less than" *)
  address_le: A -> A -> Prop ;

  address_le_dec: forall a b, {address_le a b}+{~ address_le a b};

  (* Generates of set of addresses in the given range. NOTE: unlike
     functoin with same name in capablities.lem, the 2nd argument is
     end of interval (exclusive), not the lenght! No error handling
     for now. We will return empty set instead. But may be later
     extended with error handling.
   *)
  address_range: A -> A -> {l:list A| NoDup l} ;
  }.

Section AddressHelpers.
  Context `{ADR: Address A}.

  (* Set of addresses type aliase *)
  Definition address_set := {l:list A| NoDup l} .

  (* Empty address set constant *)
  Definition empty_address_set: address_set := @exist _ _ [] (NoDup_nil _).

  (* boolean versoin of [address_le] preficate *)
  Definition address_leb: A -> A -> bool :=
    fun a b => if address_le_dec a b then true else false.

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
     memory region, or None if empty *)
  get_bounds: C -> option (address*address);

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
  Context `{ARCH: Arch A}.
  Context `{ADR: Address address}.
  Context `{PERM: @Permission P A ARCH}.
  Context `{CAPA: @Capability C _ ARCH  _ ADR _ PERM}.

  Definition get_mem_region `{Capability C} (c:C): address_set
    := match get_bounds c with
       | Some (from,to) => address_range from to
       | None => empty_address_set
       end.

End CapabilityProperties.
