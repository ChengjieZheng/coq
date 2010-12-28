
Require Export Ind.
Import Playground1.

Inductive and (P Q : Prop) : Prop :=
		conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.

Theorem and_example : 
	(ev O) /\ (ev (S (S O))).
Proof.
	split.
		apply ev_0.
		apply ev_SS. apply ev_0.
	Qed.

Print and_example.

Theorem proj1 : forall P Q : Prop,
	P /\ Q -> P.
Proof.
	intros P Q H.
	inversion H as [HP HQ].
	apply HP. Qed.

Theorem proj2 : forall P Q : Prop,
	P /\ Q -> Q.
Proof.
	intros P Q H.
	inversion H as (HP, HQ).
	apply HQ. Qed.

Theorem and_commut : forall P Q : Prop,
	P /\ Q -> Q /\ P.
Proof.
	intros P Q H.
	inversion H as (HP, HQ).
	split.
	 apply HQ.
	 apply HP.
Qed.

Print and_commut.

Theorem and_assoc : forall P Q R : Prop,
	P /\  (Q /\ R) -> (P /\ Q) /\ R.
Proof.
	intros P Q R H.
	inversion H as [HP [HQ HR]].
	split.
		split.
 			apply HP.
 			apply HQ.
		apply HR.
Qed.

Theorem even_ev : forall n : nat,
	(even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
	induction n.
	Case "n = O".
		split.
		SCase "even O -> ev O".
	 		intros H.
			apply ev_0.
		SCase "even (S O) -> ev (S O)".
			intros contra.
			inversion contra.
	Case "n = S n'".
		inversion IHn as [IH1 IH2].
		split.
		SCase "left".
			apply IH2.
		SCase "right".
			intros H.
			unfold even in H.
			simpl in H.
			apply ev_SS.
			apply IH1.
			apply H.
Qed.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) : type_scope.

Theorem iff_implies : forall P Q : Prop,
	(P <-> Q) -> P -> Q.
Proof.
	intros P Q H.
	inversion H as [HAB HBA].
	apply HAB. Qed.

Theorem iff_sym : forall P Q : Prop,
	(P <-> Q) -> (Q <-> P).
Proof.
	intros P Q H.
	inversion H as [HAB HBA].
	split.
		Case "->". apply HBA.
		Case "<-". apply HAB. Qed.

Theorem iff_refl : forall P : Prop,
	P <-> P.
Proof.
	intros P.
	unfold iff.
	split.
	 intros H.
	 apply H.
	 
	 intros H.
	 apply H.
Qed.

Theorem MyProp_iff_ev : forall n, MyProp n <-> ev n.
Proof.
	intros n.
	unfold iff.
	split.
	 apply ev_MyProp.
	 apply MyProp_ev.
	Qed.

Print MyProp_iff_ev.

Inductive or (P Q : Prop) : Prop :=
	| or_introl : P -> or P Q
	| or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Theorem or_commut : forall P Q : Prop,
	P \/ Q -> Q \/ P.
Proof.
	intros P Q H.
	inversion H as [HP | HQ].
		Case "right". apply or_intror. apply HP.
		Case "left". apply or_introl. apply HQ. Qed.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
	P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
	intros P Q R.
	intros H.
	inversion H as [HP | [HQ HR]].
		Case "left". split.
			SCase "left". left. apply HP.
			SCase "right". left. apply HP.
		Case "right". split.
			SCase "left". right. apply HQ.
			SCase "right". right. apply HR. Qed.

Print or_distributes_over_and_1.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
	(P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
	intros P Q R.
	intros H.
	inversion H as (H1, H2).
	inversion H1 as [H11| H12].
	left.
		apply H11.
  inversion H2 as [H21| H22].
	 left.
		 apply H21.
			   
	 right.
		 split.
				apply H12.
			  apply H22.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
	P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
	intros P Q R.
	unfold iff.
	split.
	 apply or_distributes_over_and_1.
	 apply or_distributes_over_and_2.
Qed.

Theorem andb_true__and : forall b c,
	andb b c = true -> b = true /\ c = true.
Proof.
	intros b c H.
	destruct b.
		Case "b = true". destruct c.
			SCase "c = true". apply conj. reflexivity. reflexivity.
			SCase "c = false". inversion H.
		Case "b = false". inversion H. Qed.

Theorem and__andb_true : forall b c,
	b = true /\ c = true -> andb b c = true.
Proof.
	intros b c H.
	inversion H.
	rewrite H0.
	rewrite H1.
	reflexivity.
	Qed.

Theorem andb_false : forall b c,
	andb b c = false -> b = false \/ c = false.
Proof.
	intros b c.
	intros H.
	unfold andb in H.
	destruct b.
	right.
  	apply H.
	left.
	  reflexivity.
Qed.

Theorem orb_true : forall b c,
	orb b c = true -> b = true \/ c = true.
Proof.
	intros b c.
	unfold orb.
	destruct b.
	Case "b = true".
  	intros H.
		left.
		reflexivity.  
	Case "b = false".
		intros H.
		right.
		apply H.
Qed.

Theorem orb_false : forall b c,
	orb b c = false -> b = false /\ c = false.
Proof.
	intros b c.
	unfold orb.
	destruct b.
	Case "b = true".
		intros contra.
		inversion contra.
	Case "b = false". 
		intros H.
	  split.
		SCase "left".
			reflexivity.
		SCase "right".
		apply H.
Qed.

Inductive False : Prop := .

Theorem False_implies_nonsense :
	False -> (S (S O)) + (S (S O)) = (S (S (S (S (S O))))).
Proof.
	intros contra.
	inversion contra.
	Qed.

Theorem nonsense_implies_False :
	(S (S O)) + (S (S O)) = (S (S (S (S (S O))))) -> False.
Proof.
	intros contra.
	inversion contra.
	Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
	False -> P.
Proof.
	intros P contra.
	inversion contra. Qed.

Definition True : Prop := forall (P:Prop), P -> P.

Theorem true_theorem:
	True.
Proof.
	unfold True.
	intros P H.
	apply H.
	Qed.

Definition not (P : Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Theorem not_False :
	~ False.
Proof.
	unfold not.
	intros H.
	inversion H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
	(P /\ ~P) -> P.
Proof.
	intros P Q H.
	inversion H as [HP HNA].
	unfold not in HNA.
	apply HNA in HP.
	inversion HP.
	Qed.

Theorem double_neg : forall P : Prop,
	P -> ~~P.
Proof.
	intros P H.
	unfold not.
	intros G.
	apply G.
	apply H.
Qed.

Theorem contrapositive : forall P Q : Prop,
	(P -> Q) -> (~Q -> ~P).
Proof.
	intros P Q.
	intros H.
	unfold not.
	intros G.
	intros G2.
	apply G.
	apply H.
	apply G2.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
	~(P /\ ~P).
Proof.
	intros P.
	unfold not.
	intros H.
	inversion H as (H1, H2).
	apply H2.
	apply H1.
Qed.

Theorem five_not_even :
	~ ev (S (S (S (S (S O))))).
Proof.
	unfold not.
	intros Hev5.
	inversion Hev5 as [| n Hev3 Heqn].
	inversion Hev3 as [| n' Hev1 Heqn'].
	inversion Hev1. Qed.

Theorem ev_not_ev_S : forall n,
	ev n -> ~ev (S n).
Proof.
	unfold not. intros n H.
	induction H.
  intros contra.
	inversion contra.
		 
	intros G.
	inversion G.
	apply IHev in H1.
	apply H1.
Qed. 

Definition peirce := forall P Q: Prop, 
 ((P->Q)->P)->P.
Definition classic := forall P:Prop, 
	~~P -> P.
Definition excluded_middle := forall P:Prop, 
	P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, 
	~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, 
	(P->Q) -> (~P\/Q).

Theorem excluded_middle_classic : forall (P : Prop),
		P \/ ~P -> (~~P -> P).
Proof.
intros P.
intros H.
inversion H.
intros G.
apply H0.

intros G.
unfold not in G.
unfold not in H0.
apply G in H0.
inversion H0.
Qed.

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
	b <> false -> b = true.
Proof.
	intros b H.
	destruct b.
	Case "b = true". reflexivity.
	Case "b = false".
		unfold not in H.
		apply ex_falso_quodlibet.
		apply H. reflexivity. Qed.

Theorem not_eq_beq_false : forall n n' : nat,
		n <> n' ->
			beq_nat n n' = false.
Proof.
induction n.
destruct n'.
intros H.
unfold not in H.
apply ex_falso_quodlibet.
apply H.
reflexivity.

intros H.
simpl.
reflexivity.

destruct n'.
intros H.
simpl.
reflexivity.

intros H.
simpl.
apply IHn.
unfold not.
unfold not in H.
intros H2.
apply H.
rewrite H2.
reflexivity.
Qed.

Theorem beq_false_not_eq : forall n m,
	false = beq_nat n m -> n <> m.
Proof.
induction n.
destruct m.
intros H.
inversion H.

simpl.
intros H.
unfold not.
intros H2.
inversion H2.

destruct m.
simpl.
intros H1.
unfold not.
intros H2.
inversion H2.

simpl.
intros H.
apply IHn in H.
unfold not in H.
unfold not.
intros H2.
inversion H2.
apply H.
rewrite H1.
reflexivity.
Qed.

Inductive ex (X:Type) (P : X -> Prop) : Prop :=
	ex_intro : forall (witness:X), P witness -> ex X P.

Definition some_nat_is_even : Prop :=
	ex nat ev.

Definition snie : some_nat_is_even :=
	ex_intro _ ev (S (S (S (S O)))) (ev_SS (S (S O)) (ev_SS O ev_0)).

Notation "'exists' x , p" := (ex _ (fun x => p))
	(at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
	(at level 200, x ident, right associativity) : type_scope.

Definition p : ex nat (fun n => ev (S n)) :=
		ex_intro _ (fun n => ev (S n)) (S O) (ev_SS O ev_0).

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
	(forall x, P x) -> ~(exists x, ~ P x).
Proof.
intros X.
intros P.
intros H.
unfold not.
intros H1.
inversion H1.
apply H0.
apply H.
Qed.

Theorem not_exists_dist :
	excluded_middle ->
		forall (X:Type) (P : X -> Prop),
			~(exists x, ~ P x) -> (forall x, P x).
Proof.
unfold excluded_middle.
intros H.
intros X P.
unfold not.
intros H1.
intros x.
assert (P x \/ ~ P x).
apply H.

inversion H0.
apply H2.

apply ex_falso_quodlibet.
apply H1.
unfold not in H2.
exists x.
apply H2.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
	(exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
intros X.
intros P Q.
unfold iff.
split.
intros H.
inversion H.
inversion H0.
left.
exists witness.
apply H1.

right.
exists witness.
apply H1.

intros H.
inversion H.
inversion H0.
exists witness.
left.
apply H1.

inversion H0.
exists witness.
right.
apply H1.
Qed.

Module MyEquality.

Inductive eq (X : Type) : X -> X -> Prop :=
	refl_equal : forall x, eq X x x.

Notation "x = y" := (eq _ x y) (at level 70, no associativity) : type_scope.

Inductive eq' (X:Type) (x:X) : X -> Prop :=
	refl_equal' : eq' X x x.

Notation "x =' y" := (eq' _ x y) (at level 70, no associativity) : type_scope.

Theorem two_defs_of_eq_coincide : forall (X:Type) x y,
		eq X x y <-> eq' X x y.
Proof.
intros X.
intros x y.
unfold iff.
split.
intros H.
destruct H.
apply refl_equal'.

intros H.
inversion H.
rewrite H0.
apply refl_equal.
Qed.

Definition four : (S (S O)) + (S (S O)) = (S O) + (S (S (S O))) :=
	refl_equal nat (S (S (S (S O)))).
Definition singleton : forall (X : Set) (x:X), [] ++ [x] = x::[] :=
	fun (X:Set) (x:X) => refl_equal (list X) [x].

End MyEquality.

Inductive le (n:nat) : nat -> Prop :=
	| le_n : le n n
	| le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 :
	(S (S (S O))) <= (S (S (S O))).
Proof.
	apply le_n. Qed.

Theorem test_le2 :
	(S (S (S O))) <= (S (S (S (S (S (S O)))))).
Proof.
	apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
	~((S (S O)) <= (S O)).
Proof.
	intros H.
	inversion H.
	inversion H1. Qed.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
	sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n : nat) : nat -> Prop :=
	| nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
	| ne_1 : ev (S n) -> next_even n (S n)
	| ne_2 : ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
	total_relation1 : forall (n m:nat), total_relation n m.

Inductive empty_relation (n:nat) : nat -> Prop := .
	
Inductive R : nat -> nat -> nat -> Prop :=
	| c1 : R O O O
	| c2 : forall m n o, R m n o -> R (S m) n (S o)
	| c3 : forall m n o, R m n o -> R m (S n) (S o)
	| c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
	| c5 : forall m n o, R m n o -> R n m o.

Theorem R_prov1:
	R (S O) (S O) (S (S O)).
Proof.
apply c4.
apply c3.
apply c3.
apply c2.
apply c2.
apply c1.
Qed.

(*
Theorem R_prov2:
	R (S (S O)) (S (S O)) (S (S (S (S (S (S O)))))).
Proof.
  not provable I think
	"n + m" must be equal to "o"
 *)

Theorem R_fact: forall (m n o : nat),
	R m n o -> m + n = o.
Proof.
	intros m n o H.
	induction H.
	reflexivity.

	simpl.
	rewrite IHR.
	reflexivity.

	simpl.
	rewrite <- plus_n_Sm.
	rewrite IHR.
	reflexivity.

	simpl in IHR.
	rewrite <- plus_n_Sm in IHR.
	simpl in IHR.
	inversion IHR.
	reflexivity.

	simpl.
	rewrite plus_comm.
	apply IHR.
Qed.


