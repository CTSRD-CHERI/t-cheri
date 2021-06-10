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

Definition w64_in_interval (r:w64_interval): Ensembles.Ensemble w64 :=
  match r with
  | Empty_Interval _ => Ensembles.Empty_set w64
  | Incl_Interval base top H => fun x => x <= top /\ base <= x
  end.

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

Definition CAP_SEAL_TYPE_UNSEALED:otype := $0.
Definition CAP_SEAL_TYPE_RB:otype       := $1. (* register-based branch *)
Definition CAP_SEAL_TYPE_LPB:otype      := $2. (* load pair and branch *)
Definition CAP_SEAL_TYPE_LB:otype       := $3. (* load and branch *)

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


Record MCapability :=
  {
  is_valid: bool;

  (* "Union" type of two values *)
  value_addr: w64;
  value_otype: MObjectType;

  bounds: w64_interval; (* TODO: alignment *)
  perms: MPermission;
  is_global: bool;
  is_execuvite : bool; (* Morello-spefic? *)

  obj_type : otype;
  }.

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

(* take [otype_size] least significant bits of [w64] *)
Definition w64_to_ot_cast (x:w64): otype :=
  split1 otype_size (w64_size-otype_size) (eq_rec_r word x eq_refl).

Program Definition otype_of_w64 (ot:w64): option MObjectType
  := match is_Reserved_dec (w64_to_ot_cast ot) with
     | left _ => None
     | right p => Some (@exist _ _ (w64_to_ot_cast ot) _)
     end.

Program Definition address_of_otype (ot:MObjectType): w64
  := zext (proj1_sig ot) (w64_size-otype_size).

Definition clear_global (c:MCapability): MCapability :=
  {|
  is_valid := is_valid c;
  value_addr := value_addr c;
  value_otype := value_otype c;
  bounds := bounds c;
  perms := perms c;
  is_global := false ;
  is_execuvite := is_execuvite c;
  obj_type := obj_type c
  |}.

Definition unseal (c:MCapability): MCapability :=
  {|
  is_valid := is_valid c;
  value_addr := value_addr c;
  value_otype := value_otype c;
  bounds := bounds c;
  perms := perms c;
  is_global := is_global c;
  is_execuvite := is_execuvite c;
  obj_type := CAP_SEAL_TYPE_UNSEALED
  |}.

Definition seal (c:MCapability) (ot:MObjectType): MCapability :=
  {|
  is_valid := is_valid c;
  value_addr := value_addr c;
  value_otype := value_otype c;
  bounds := bounds c;
  perms := perms c;
  is_global := is_global c;
  is_execuvite := is_execuvite c;
  obj_type := proj1_sig ot
  |}.

Program Definition get_value (c:MCapability) : @CapValue MObjectType w64 :=
  if orb (permits_seal (perms c)) (permits_unseal (perms c))
  then CapToken (value_otype c)
  else CapAddress (value_addr c).

Lemma seal_perms_value_type (c: MCapability):
  permits_seal (perms c) = true \/ permits_unseal (perms c) = true
  <->
  (exists t : MObjectType, get_value  c = CapToken t).
Proof.
  split; unfold get_value; intros.
  -
    rewrite <- Bool.orb_true_iff in H.
    rewrite H.
    eauto.
  -
    destruct H.
    break_if.
    +
      apply Bool.orb_true_iff.
      auto.
    +
      inversion H.
Qed.

Instance CCapability_MCapability :
  @CCapability MObjectType w64 CAddress_w64 MPermission _ (MCapability) :=
  {|
  Capabilities.is_valid := fun c => is_valid c = true ;
  Capabilities.get_bounds := fun c => bounds c ;
  Capabilities.get_perms := fun c => perms c ;
  Capabilities.get_value := fun c => get_value c;
  Capabilities.get_seal := fun c => Seal_of_otype (obj_type c) ;
  Capabilities.is_global := fun c => is_global c = true ;
  Capabilities.address_of_otype := address_of_otype ;
  Capabilities.seal_perms_value_type := seal_perms_value_type;
  |}.

Program Instance CCapabilityOps_MCapability :
  @CCapabilityOps _ _ _ _ _ _ CCapability_MCapability :=
  {|
  Capabilities.seal := seal ;
  Capabilities.unseal := unseal ;
  Capabilities.clear_global := clear_global;
  |}.


(* --- Decoding/Encoding --- *)

Definition encode: MCapability -> option (word 128).
  (* TODO *) Admitted.
Definition decode: word 128 -> option MCapability.
  (* TODO *) Admitted.
