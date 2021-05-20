(* Specialization of Morello CHERI *)

Require Import Cheri.Capabilities.

Require Import bbv.Word.

Definition w64_size: nat := 64.
Definition w64 := word w64_size.
Definition w64_lt: w64 -> w64 -> Prop := @wlt w64_size.
Definition w64_interval : Type := Interval w64_lt.

(* encoded object type is 15 bits *)
Definition otype : Type. Admitted.

(* --- "Logical view of Capablities in Morello. --- *)

Record MPermission :=
  {
  permits_load: bool;
  permits_store: bool;
  permits_execute: bool ;
  permits_load_cap: bool;
  permits_store_cap: bool;
  permits_store_local_cap: bool;
  permits_seal: bool;
  permits_unseal: bool;
  permits_system_access: bool;

  permits_ccall: bool; (* called "permoit_branch_sealer_pair" in Morello *)

  permit_compartment_id: bool; (* Morello-spefic? *)
  permit_mutable_load : bool; (* Morello-spefic? *)

  (* TODO: User[N] *)
  }.


Instance CPermissoin_MPermission:
  CPermission(MPermission) :=
  {|
  Capabilities.permits_execute :=
    fun p : MPermission => permits_execute p = true;
  Capabilities.permits_ccall :=
    fun p : MPermission => permits_ccall p = true;
  Capabilities.permits_load :=
    fun p : MPermission => permits_load p = true;
  Capabilities.permits_load_cap :=
    fun p : MPermission => permits_load_cap p = true;
  Capabilities.permits_seal :=
    fun p : MPermission => permits_seal p = true;
  Capabilities.permits_store :=
    fun p : MPermission => permits_store p = true;
  Capabilities.permits_store_cap :=
    fun p : MPermission => permits_store_cap p = true;
  Capabilities.permits_store_local_cap :=
    fun p : MPermission => permits_store_local_cap p = true;
  Capabilities.permits_system_access :=
    fun p : MPermission => permits_system_access p = true;
  Capabilities.permits_unseal :=
    fun p : MPermission => permits_unseal p = true
  |}.

Record MCapability :=
  {
  is_valid: bool;
  bounds: w64_interval;
  permisoins: MPermission;
  is_global: bool;
  is_execuvite : bool; (* Morello-spefic? *)
  seal: @CapSeal otype ;
  (* TODO: Flags *)
  }.

(* --- Decoding/Encoding --- *)

Definition encode: MCapability -> option (word 128).
  (* TODO *) Admitted.
Definition decode: word 128 -> option MCapability.
  (* TODO *) Admitted.
