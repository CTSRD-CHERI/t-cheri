(* Specialization of Morello CHERI *)

Require Import Cheri.Capabilities.
Require Import StructTact.StructTactics.

Require Import bbv.Word.
Import bbv.Word.Notations.

Local Open Scope word_scope.

Definition w64_size: nat := 64.
Definition w64 := word w64_size.
Definition w64_lt: w64 -> w64 -> Prop := @wlt w64_size.
Definition w64_interval : Type := Interval w64_lt.

Lemma w64_lt_irref: forall x:w64, ~ w64_lt x x.
Proof.
  intros x.
  unfold w64_lt.
  apply eq_le.
  reflexivity.
Qed.

Definition w64_in_interval : w64_interval -> Ensembles.Ensemble w64.
  (* TODO *)
Admitted.

Instance CAddress_w64 : CAddress(w64) :=
  {|
  address_lt := w64_lt;
  address_lt_irref := w64_lt_irref;
  addresses_in_interval := w64_in_interval
  |}.

(* This is "encoded" object type which encodes both
   sealing type and object type value *)
Definition otype_size: nat := 15. (* CAP_VALUE_NUM_BITS *)
Definition otype := word otype_size.

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


Instance CPermissoin_MPermission: CPermission(MPermission) :=
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
  address: w64;
  bounds: w64_interval;
  perms: MPermission;
  is_global: bool;
  is_execuvite : bool; (* Morello-spefic? *)

  obj_type : otype;
  }.

Definition CAP_SEAL_TYPE_UNSEALED:otype := $0.
Definition CAP_SEAL_TYPE_RB:otype       := $1.
Definition CAP_SEAL_TYPE_LPB:otype      := $2.
Definition CAP_SEAL_TYPE_LB:otype       := $3.

Definition is_Reserved_OT (v:otype) :=
  v = CAP_SEAL_TYPE_UNSEALED \/
  v = CAP_SEAL_TYPE_RB       \/
  v = CAP_SEAL_TYPE_LPB      \/
  v = CAP_SEAL_TYPE_LB       .

Definition is_Reserved_dec (x:otype) : {is_Reserved_OT x}+{~is_Reserved_OT x}.
Proof.
  unfold otype, is_Reserved_OT in *.
  destruct (weq x CAP_SEAL_TYPE_UNSEALED ); auto.
  destruct (weq x CAP_SEAL_TYPE_RB       ); auto.
  destruct (weq x CAP_SEAL_TYPE_LPB      ); auto.
  destruct (weq x CAP_SEAL_TYPE_LB       ); auto.
  right.
  intros H.
  repeat destruct H;auto.
Qed.

(* Logical object type, exlcuding special values *)
Definition MObjectType := {v:otype | ~ is_Reserved_OT v}.
Instance CObjectType_MObjectType:
  CObjectType(MObjectType).
Qed.

(* @thomas "In the Morello proof we treat RB as sentry and {LPB,LB} as indirect sentries."
   TODO: probably we can do this more elegantly w/o using Program.
*)
Program Definition Seal_of_otype (x:otype): (@CapSeal MObjectType)
  :=
    if weq x CAP_SEAL_TYPE_UNSEALED then Cap_Unsealed
    else (if weq x CAP_SEAL_TYPE_RB then Cap_SEntry
          else (if weq x CAP_SEAL_TYPE_LPB then Cap_Indirect_SEntry
                else (if weq x CAP_SEAL_TYPE_LB then Cap_Indirect_SEntry
                      else Cap_Sealed (@exist _ _ x _)))).
Next Obligation.
  intro R.
  inversion R; try  congruence.
  destruct H3; try congruence.
  destruct H3; try congruence.
Defined.

Definition w64_to_ot_cast: w64 -> otype.
  (* TODO: zero padding *)
Admitted.

Program Definition otype_of_w64 (ot:w64): option MObjectType
  := match is_Reserved_dec (w64_to_ot_cast ot) with
     | left _ => None
     | right p => Some (@exist _ _ (w64_to_ot_cast ot) _)
     end.

Definition clear_global (c:MCapability): MCapability :=
  {|
  is_valid := is_valid c;
  address := address c;
  bounds := bounds c;
  perms := perms c;
  is_global := false ;
  is_execuvite := is_execuvite c;
  obj_type := obj_type c
  |}.

Definition unseal (c:MCapability): MCapability :=
  {|
  is_valid := is_valid c;
  address := address c;
  bounds := bounds c;
  perms := perms c;
  is_global := is_global c;
  is_execuvite := is_execuvite c;
  obj_type := CAP_SEAL_TYPE_UNSEALED
  |}.

Definition seal (c:MCapability) (ot:MObjectType): MCapability :=
  {|
  is_valid := is_valid c;
  address := address c;
  bounds := bounds c;
  perms := perms c;
  is_global := is_global c;
  is_execuvite := is_execuvite c;
  obj_type := proj1_sig ot
  |}.

Program Instance CCapability_MCapability :
  @CCapability MObjectType w64 CAddress_w64 MPermission (MCapability) :=
  {|
  Capabilities.is_valid := fun c => is_valid c = true ;
  Capabilities.get_bounds := fun c => bounds c ;
  Capabilities.get_perms := fun c => perms c ;
  Capabilities.get_address := fun c => address c ;
  Capabilities.get_seal := fun c => Seal_of_otype (obj_type c) ;
  Capabilities.seal := seal ;
  Capabilities.unseal := unseal ;
  Capabilities.is_global := fun c => is_global c = true ;
  Capabilities.clear_global := clear_global;
  Capabilities.otype_of_address := otype_of_w64 ;
  |}.

(* --- Decoding/Encoding --- *)

Definition encode: MCapability -> option (word 128).
  (* TODO *) Admitted.
Definition decode: word 128 -> option MCapability.
  (* TODO *) Admitted.
