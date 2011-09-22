
Require Export Smallstep.

Hint Resolve 1.


Hint Constructors refl_step_closure.
Hint Resolve beq_id_eq beq_id_false_not_eq.

Tactic Notation "normalize" := 
   repeat (eapply rsc_step ; 
                      [ (eauto 10; fail) | (instantiate; simpl)]);
      apply rsc_refl.

Module Types.

Inductive tm : Type :=
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_zero : tm
  | tm_succ : tm -> tm
  | tm_pred : tm -> tm
  | tm_iszero : tm -> tm.

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue tm_true
  | bv_false : bvalue tm_false.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tm_zero
  | nv_succ : forall t, nvalue t -> nvalue (tm_succ t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tm_if tm_true t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tm_if tm_false t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tm_if t1 t2 t3) ==> (tm_if t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tm_succ t1) ==> (tm_succ t1')
  | ST_PredZero :
      (tm_pred tm_zero) ==> tm_zero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tm_pred (tm_succ t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tm_pred t1) ==> (tm_pred t1')
  | ST_IszeroZero :
      (tm_iszero tm_zero) ==> tm_true
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tm_iszero (tm_succ t1)) ==> tm_false
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tm_iszero t1) ==> (tm_iszero t1')

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" 
  | Case_aux c "ST_Succ" | Case_aux c "ST_PredZero"
  | Case_aux c "ST_PredSucc" | Case_aux c "ST_Pred" 
  | Case_aux c "ST_IszeroZero" | Case_aux c "ST_IszeroSucc"
  | Case_aux c "ST_Iszero" ].

Hint Constructors step.

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

Example some_tm_is_stuck :
  exists t, stuck t.
Proof.
   exists (tm_succ tm_true).
   unfold stuck.
   split.
    unfold normal_form.
    intros.
    unfold not.
    intros H.
    inversion H.
    inversion H0.
    subst.
    inversion H2.

    unfold not.
    intros H.
    inversion H.
     inversion H0.

     inversion H0.
     inversion H2.
Qed.

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
induction t.
 intros H.
 unfold normal_form.
 intros H1.
 inversion H1.
 inversion H0.
 
 intros H.
 intros H1.
 inversion H1.
 inversion H0.
 
 intros H.
 inversion H.
  inversion H0.
  
  inversion H0.
  
 intros H.
 intros H1.
 inversion H1.
 inversion H0.
 
 intros H.
 intros H1.
 inversion H1.
 inversion H0.
 apply IHt.
  inversion H.
   inversion H5.
   
   inversion H5.
   unfold value.
   right.
   assumption.
   
  exists t1'.
  assumption.
  
 intros H.
 inversion H.
  inversion H0.
  
  inversion H0.
  
 intros H.
 inversion H.
  inversion H0.
  
  inversion H0.
Qed.

Theorem step_deterministic:
  partial_function step.
Proof with eauto.
unfold partial_function.
induction x.
 intros.
 inversion H.
 
 intros.
 solve by inversion.
 
 intros.
 inversion H.
  subst.
  inversion H0.
   subst.
   auto.
   
   subst.
   inversion H5.
   
  subst.
  inversion H0.
   subst.
   reflexivity.
   
   auto.
   subst.
   inversion H5.
   
  subst.
  auto.
  subst.
  inversion H0.
   subst.
   inversion H.
    inversion H5.
    
    inversion H2.
    
   subst.
   inversion H5.
   
   subst.
   assert (t1' = t1'0).
    apply IHx1.
     assumption.
     
     assumption.
     
    auto.
    rewrite H1.
    reflexivity.
    
 intros.
 inversion H.
 
 intros.
 inversion H.
 subst.
 inversion H0.
 subst.
 assert (t1' = t1'0).
  apply IHx.
   assumption.
   
   assumption.
   
  rewrite H1.
  reflexivity.
  
 intros.
 inversion H.
  inversion H0.
   reflexivity.
   
   subst.
   inversion H0.
    reflexivity.
    
    inversion H2.
    
   subst.
   inversion H4.
   
  subst.
  inversion H.
   subst.
   inversion H0.
    subst.
    reflexivity.
    
    subst.
    inversion H5.
    subst.
    subst.
    assert (step_normal_form y1).
     apply value_is_nf.
     right.
     assumption.
     
     unfold normal_form in H1.
     apply ex_falso_quodlibet.
     apply H1.
     exists t1'0.
     assumption.
     
   subst.
   inversion H0.
    subst.
    reflexivity.
    
    subst.
    assert (t1' = t1'0).
     apply IHx.
      assumption.
      
      assumption.
      
     rewrite H1.
     reflexivity.
     
  subst.
  inversion H0.
   subst.
   inversion H2.
   
   subst.
   inversion H0.
    subst.
    assert (step_normal_form y2).
     apply value_is_nf.
     right.
     assumption.
     
     apply ex_falso_quodlibet.
     apply H1.
     inversion H2.
     exists t1'0.
     assumption.
     
    subst.
    assert (t1' = t1'0).
     apply IHx.
      assumption.
      
      assumption.
      
     rewrite H1.
     reflexivity.
     
   subst.
   assert (t1' = t1'0).
    apply IHx.
     assumption.
     
     assumption.
     
    rewrite H1.
    reflexivity.
    
 intros.
 inversion H.
  subst.
  inversion H0.
   reflexivity.
   
   inversion H2.
   
  subst.
  inversion H0.
   reflexivity.
   
   subst.
   assert (step_normal_form t1).
    apply value_is_nf.
    right.
    assumption.
    
    apply ex_falso_quodlibet.
    apply H1.
    inversion H3.
    exists t1'0.
    assumption.
    
  subst.
  inversion H0.
   subst.
   inversion H2.
   
   subst.
   assert (step_normal_form t1).
    apply value_is_nf.
    right.
    assumption.
    
    apply ex_falso_quodlibet.
    apply H1.
    inversion H2.
    exists t1'0.
    assumption.
    
   subst.
   assert (t1' = t1'0).
    apply IHx.
     assumption.
     
     assumption.
     
    rewrite H1.
    reflexivity.
Qed.

Inductive ty : Type := 
  | ty_Bool : ty
  | ty_Nat : ty.
  
Inductive has_type : tm -> ty -> Prop :=
 | T_True : 
      has_type tm_true ty_Bool
 | T_False : 
      has_type tm_false ty_Bool
 | T_If : forall t1 t2 t3 T,
      has_type t1 ty_Bool ->
      has_type t2 T ->
      has_type t3 T ->
      has_type (tm_if t1 t2 t3) T
 | T_Zero : 
      has_type tm_zero ty_Nat
 | T_Succ : forall t1,
      has_type t1 ty_Nat ->
      has_type (tm_succ t1) ty_Nat
 | T_Pred : forall t1,
      has_type t1 ty_Nat ->
      has_type (tm_pred t1) ty_Nat
 | T_Iszero : forall t1,
      has_type t1 ty_Nat ->
      has_type (tm_iszero t1) ty_Bool.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
 first;
 [ Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
 | Case_aux c "T_Zero" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
 | Case_aux c "T_Iszero" ].

Hint Constructors has_type.

Example has_type_1 : 
 has_type (tm_if tm_false tm_zero (tm_succ tm_zero)) ty_Nat.
Proof.
 apply T_If.
   apply T_False.
   apply T_Zero.
   apply T_Succ.
     apply T_Zero.
Qed.

Example has_type_not : 
 ~ has_type (tm_if tm_false tm_zero tm_true) ty_Bool.
Proof.
 intros Contra. solve by inversion 2. Qed.
 
Example succ_hastype_nat__hastype_nat : forall t,
has_type (tm_succ t) ty_Nat ->
has_type t ty_Nat.
Proof.
intros.
inversion H.
assumption.
Qed.

Theorem progress : forall t T,
  has_type t T ->
  value t \/ exists t', t ==> t'.
Proof with auto.
  intros t T HT.
  has_type_cases (induction HT) Case...
  (* The cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  Case "T_If".
    right. destruct IHHT1.
    SCase "t1 is a value". destruct H.
      SSCase "t1 is a bvalue". destruct H.
        SSSCase "t1 is tm_true".
          exists t2...
        SSSCase "t1 is tm_false".
          exists t3...
      SSCase "t1 is an nvalue".
        solve by inversion 2. (* on H and HT1 *)
    SCase "t1 can take a step".
      destruct H as [t1' H1].
      exists (tm_if t1' t2 t3)...

      inversion IHHT.
        left.
        right.
        inversion H.
         inversion H0.
          subst.
          inversion HT.

          subst.
          inversion HT.

         apply nv_succ.
         assumption.

        right.
        inversion H.
        exists (tm_succ x).
        auto.

       inversion IHHT.
        auto.
        inversion H.
         solve by inversion 2.

         right.
         inversion H0.
          exists tm_zero.
          auto.

          subst.
          exists t.
          auto.

        right.
        inversion H.
        exists (tm_pred x).
        auto.

       inversion IHHT.
        inversion H.
         inversion H0.
          solve by inversion 2.

          solve by inversion 2.

         inversion H0.
          right.
          exists tm_true.
          auto.

          right.
          exists tm_false.
          auto.

        right.
        inversion H.
        exists (tm_iszero x).
        auto.
Qed.

Theorem preservation : forall t t' T,
  has_type t T ->
  t ==> t' ->
  has_type t' T.
Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  has_type_cases (induction HT) Case; 
         (* every case needs to introduce a couple of things *)
         intros t' HE; 
         (* and we can deal with several impossible
            cases all at once *)
         try (solve by inversion).
    Case "T_If". inversion HE; subst.
      SCase "ST_IFTrue". assumption.
      SCase "ST_IfFalse". assumption.
      SCase "ST_If". apply T_If; try assumption.
        apply IHHT1; assumption.
        inversion HE.
         apply T_Succ.
         apply IHHT.
         assumption.

         inversion HE.
          apply T_Zero.

          subst.
          subst.
          assert (forall t, nvalue t -> has_type t ty_Nat).
           intros.
           induction H.
            apply T_Zero.

            apply T_Succ.
            assumption.

           apply H.
           assumption.

          subst.
          apply T_Pred.
          apply IHHT.
          assumption.

         inversion HE.
          apply T_True.

          apply T_False.

          subst.
          apply T_Iszero.
          apply IHHT.
          assumption.
Qed.

Theorem preservation' : forall t t' T,
  has_type t T ->
  t ==> t' ->
  has_type t' T.
Proof with eauto.

intros t t'.
intros T.
intros H1.
generalize dependent t'.
intros.
generalize dependent H1.
generalize dependent T.
induction H.
 intros T.
 intros H.
 inversion H.
 assumption.
 
 intros T H.
 inversion H.
 assumption.
 
 intros T H1.
 inversion H1.
 apply T_If.
  apply IHstep.
  assumption.
  
  assumption.
  
  assumption.
  
 intros T.
 intros H1.
 inversion H1.
 apply T_Succ.
 apply IHstep.
 assumption.
 
 intros T H.
 inversion H.
 assumption.
 
 intros T H1.
 inversion H1.
 inversion H2.
 assumption.
 
 intros T H1.
 inversion H1.
 apply T_Pred.
 apply IHstep.
 assumption.
 
 intros T H.
 inversion H.
 apply T_True.
 
 intros T H1.
 inversion H1.
 apply T_False.
 
 intros T H1.
 inversion H1.
 apply T_Iszero.
 apply IHstep.
 assumption.
Qed.

Definition stepmany := (refl_step_closure step).
Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  has_type t T ->
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.
  apply IHP. apply (preservation x y T HT H).
  unfold stuck. split; auto. Qed.
End Types.
