
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

Inductive empty_relation : nat -> nat -> Prop := .
	
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

Inductive list_merge: list nat -> list nat -> list nat -> Prop :=
	| merge0 : forall m, list_merge m [] m
	| merge1 : forall (m: list nat), list_merge [] m m
	| merge2 : forall (a b : nat) (n m o : list nat), list_merge n m o -> list_merge (a :: n) (b :: m) (a :: b :: o).

Theorem merge_t1 :
	list_merge [(S O), O, (S (S (S O)))] [O, (S (S (S (S O))))] [(S O), O, O, (S (S (S (S O)))), (S (S (S O)))].
Proof.
	apply merge2.
	apply merge2.
	apply merge0. Qed.

Theorem app_ass :forall {X: Type} (l1 l2 l3 : list X),
	(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
	intros X l1 l2 l3. induction l1 as [| n l1'].
	Case "l1 = nil".
		reflexivity.
	Case "l1 = cons n l1'".
		simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem app_cons_t : forall (l1 l2: list nat) (a : nat),
	l2 ++ (a :: l1) = (l2 ++ [a]) ++ l1.
Proof.
intros l1 l2.
generalize dependent l1.
destruct l2.
intros l1.
intros a.
simpl.
reflexivity.

intros l1 a.
simpl.
rewrite app_ass.
reflexivity.
Qed.


Theorem filter_bad : forall (l l2 : list nat) (f : nat -> bool),
	l2 <> [] -> ~(filter nat f l = l2 ++ l).
Proof.
induction l.
intros l2.
intros f.
intros H2.
simpl.
unfold not in H2.
unfold not.
destruct l2.
simpl.
intros H.
apply H2.
reflexivity.

intros H.
inversion H.

intros l2.
intros f.
intros H1.
simpl.
destruct (f x).
simpl.
intros H2.
destruct l2.
simpl in H2.
inversion H2.
assert (l = [] ++ l).
simpl.
reflexivity.

rewrite H in H0.
apply IHl in H0.
apply H0.

simpl.
apply H1.

simpl in H2.
inversion H2.
assert (l2 ++ n :: l = (l2 ++ [n]) ++ l).
apply app_cons_t.

rewrite H in H3.
apply IHl in H3.
apply H3.

simpl.
intros H4.
destruct l2.
inversion H4.

inversion H4.

assert (l2 ++ x :: l = (l2 ++ [x]) ++ l).
apply app_cons_t.

rewrite H.
apply IHl.
destruct l2.
intros H2.
inversion H2.

intros H2.
inversion H2.
Qed.

Theorem filter_theorem: forall (l l1 l2: list nat) (f : nat -> bool),
	 list_merge l1 l2 l ->
		 filter _ f l1 = l1 ->
			 filter _ f l2 = [] ->
				 filter _ f l = l1.
Proof.
 intros l l1 l2 f.
 intros H.
 induction H.
 intros H.
 intros H2.
 apply H.

 intros H1.
 intros H2.
 apply H2.

 intros H1.
 intros H2.
 simpl.
simpl in H1.
simpl in H2.
destruct (f a).
simpl.
destruct (f b).
inversion H2.

simpl.
inversion H1.
simpl.
rewrite H3.
assert (filter nat f o = n -> a :: filter nat f o = a :: n).
intros HX.
rewrite HX.
reflexivity.

apply H0.
apply IHlist_merge.
apply H3.

apply H2.

destruct (f b).
inversion H2.
assert (a :: n = [a] ++ n).
simpl.
reflexivity.

rewrite H0 in H1.
apply filter_bad in H1.
inversion H1.

intros H3.
inversion H3.
Qed.

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
	| ai_here : forall l, appears_in a (a::l)
	| ai_later : forall b l, appears_in a l -> appears_in a (b::l).

Theorem app_nil_end : forall {X:Type} (l : list X),
	l ++ [] = l.
Proof.
	intros X l.
	induction l.
	Case "l = nil".
		reflexivity.
	Case "l = cons".
		simpl. rewrite -> IHl. reflexivity. Qed.

Lemma appears_in_app : forall {X:Type} (xs ys : list X) (x:X),
	appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
intros X.
induction xs.
simpl.
intros ys x.
intros H.
right.
apply H.

simpl.
destruct ys.
intros x0.
simpl.
intros H.
left.
rewrite -> app_nil_end in H.
apply H.

intros x1.
simpl.
intros H1.
inversion H1.
simpl.
left.
apply ai_here.

subst.
apply IHxs in H0.
inversion H0.
left.
apply ai_later.
apply H.

right.
apply H.
Qed.

Lemma app_appears_in : forall {X:Type} (xs ys : list X) (x:X),
	appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
	intros X.
	induction xs.
	simpl.
	intros ys x H.
	inversion H.
	inversion H0.

	apply H0.
	simpl.
	intros ys x0.
	intros H.
	inversion H.
	inversion H0.
	apply ai_here.

	apply ai_later.
	apply IHxs.
	left.
	apply H2.

	apply ai_later.
	apply IHxs.
	right.
	apply H0.
Qed.

Definition disjoint {X:Type} (l1 l2 : list X) :=
	(forall a, appears_in a l1 -> ~(appears_in a l2)) /\ (forall a, appears_in a l2 -> ~(appears_in a l1)).

Inductive no_repeats {X:Type} : list X -> Prop :=
	| repeats_base : no_repeats []
	| repeats_in : forall a l, no_repeats l -> ~(appears_in a l) -> no_repeats (a :: l).

Theorem no_repeats1 :
	no_repeats [S O, S (S O), S (S (S O)), S (S (S (S O)))].
Proof.
apply repeats_in.
apply repeats_in.
apply repeats_in.
apply repeats_in.
apply repeats_base.

simpl.
intros H.
inversion H.

intros H.
inversion H.
inversion H1.

intros H.
inversion H.
inversion H1.
inversion H4.

intros H.
inversion H.
inversion H1.
inversion H4.
inversion H7.
Qed.

Theorem no_repeats2:
	no_repeats [true].
Proof.
apply repeats_in.
apply repeats_base.

intros H.
inversion H.
Qed.

Theorem disjoint_add: forall {X:Type} (l1 l2 : list X) (x : X),
	disjoint (x :: l1) l2 -> disjoint l1 l2.
Proof.
intros X.
destruct l1.
simpl.
intros l2 x.
intros H.
unfold disjoint.
split.
unfold disjoint in H.
inversion H.
intros a.
intros H2.
inversion H2.

intros a.
intros H2.
intros H3.
inversion H3.

simpl.
intros l2 x0.
unfold disjoint.
intros H.
destruct l2.
split.
intros a.
intros H1.
intros H2.
inversion H2.

intros a.
intros H1.
inversion H1.

split.
intros a.
inversion H.
intros H2.
apply H0.
apply ai_later.
apply H2.

intros a.
inversion H.
intros H2.
apply H1 in H2.
unfold not in H2.
intros H3.
apply H2.
apply ai_later.
apply H3.

Qed.

Theorem app_cons : forall {X : Type} (l1 l2: list X) (a : X),
	l2 ++ (a :: l1) = (l2 ++ [a]) ++ l1.
Proof.
intros X l1 l2.
generalize dependent l1.
destruct l2.
intros l1.
intros a.
simpl.
reflexivity.

intros l1 a.
simpl.
rewrite app_ass.
reflexivity.
Qed.


Theorem appears_diff : forall {X:Type} (l : list X) (a b: X),
	~ appears_in a (b :: l) -> a <> b.
Proof.
intros X.
intros l a b.
intros H.
intros H2.
unfold not in H.
apply H.
rewrite H2.
apply ai_here.
Qed.

Theorem appears_contra : forall {X : Type} (l : list X) (x : X),
	appears_in x l -> ~ appears_in x l -> False.
Proof.
intros X.
intros l x.
intros H.
intros H1.
apply H1.
apply H.
Qed.

Theorem appears_minus : forall {X:Type} (l : list X) (a b:X),
		~ appears_in a (b :: l) -> ~ appears_in a l.
Proof.
intros X.
destruct l.
intros a b.
intros H.
intros H1.
apply H.
inversion H1.

intros a b.
simpl.
intros H1.
intros H2.
apply H1.
apply ai_later.
apply H2.
Qed.

Theorem appears_add : forall {X:Type} (l : list X) (a b: X),
	~ appears_in a l /\ a <> b -> ~ appears_in a (b :: l).
Proof.
intros X.
destruct l.
intros a b.
simpl.
intros H.
inversion H.
intros H2.
apply H1.
inversion H2.
reflexivity.

inversion H4.

intros a b.
simpl.
intros H.
inversion H.
intros H2.
inversion H2.
apply H1 in H4.
apply H4.

subst.
apply appears_contra in H4.
apply H4.

apply H0.
Qed.

Theorem appears_change : forall {X : Type} (l : list X) (x y: X),
	~ appears_in y (x :: l) -> ~ appears_in y (l ++ [x]).
Proof.
intros X.
induction l.
intros x y H.
apply H.

intros x0 y.
intros H.
simpl.
assert (~ appears_in y (x :: l)).
apply appears_minus in H.
apply H.

assert (~ appears_in y l).
apply appears_minus in H0.
apply H0.

assert (y <> x0).
apply appears_diff in H.
apply H.

assert (y <> x).
apply appears_diff in H0.
apply H0.

apply appears_add.
split.
apply IHl.
assert (~ appears_in y l /\ y <> x0).
split.
apply H1.

apply H2.

apply appears_add in H4.
apply H4.

apply H3.
Qed.

Theorem not_appears_app : forall {X : Type} (l1 l2 : list X) (x : X),
	~ appears_in x (l1 ++ l2) -> ~ appears_in x (l2 ++ l1).
Proof.
intros X.
induction l1.
intros l2 x.
simpl.
intros H.
rewrite app_nil_end.
apply H.

intros l2 x0.
simpl.
intros H.
rewrite app_cons.
apply IHl1.
apply appears_change in H.
simpl in H.
rewrite app_ass in H.
apply H.
Qed.

Theorem no_appears_app : forall {X : Type} (l1 l2 : list X) (x : X),
	~ appears_in x l1 -> ~ appears_in x l2 -> ~ appears_in x (l1 ++ l2).
Proof.
intros X.
intros l1 l2.
generalize dependent l1.
induction l2.
intros l1.
intros x.
simpl.
intros H1 H2.
rewrite app_nil_end.
apply H1.

intros l1 x0.
intros H1 H2.
apply not_appears_app.
apply not_appears_app.
rewrite app_cons.
apply IHl2.
apply not_appears_app.
assert (x0 <> x).
apply appears_diff in H2.
apply H2.

simpl.
apply appears_add.
split.
apply H1.

apply H.

assert (~ appears_in x0 l2).
apply appears_minus in H2.
apply H2.

apply H.
Qed.

Theorem disjoint_minus : forall {X:Type} (l1 l2 : list X) (a b : X),
	disjoint (a :: l1) (b :: l2) -> disjoint l1 l2.
Proof.
intros X.
intros l1 l2 a b.
intros H.
unfold disjoint in H.
unfold disjoint.
split.
intros a0.
intros H1.
inversion H.
assert (appears_in a0 (b :: l1)).
apply ai_later.
apply H1.

assert (~ appears_in a0 (b :: l2)).
apply H0.
assert (appears_in a0 (a :: l1)).
apply ai_later.
apply H1.

apply H4.

assert (~ appears_in a0 l2).
apply appears_minus in H4.
apply H4.

apply H5.

intros a0.
intros H0.
inversion H.
assert (appears_in a0 (b :: l2)).
apply ai_later.
apply H0.

apply H2 in H3.
apply appears_minus in H3.
apply H3.
Qed.

Theorem disjoint_appears_in : forall {X:Type} (l1 l2 : list X) (a b : X),
	disjoint (a :: l1) (b :: l2) -> (~ appears_in a l2) /\ (~ appears_in b l1 /\ a <> b).
Proof.
intros X l1 l2 a b.
intros H.
split.
assert (disjoint l1 l2).
apply disjoint_minus in H.
apply H.

unfold disjoint in H.
unfold disjoint in H0.
inversion H.
inversion H0.
apply appears_minus with b.
apply H1.
apply ai_here.

split.
assert (disjoint l1 l2).
apply disjoint_minus in H.
apply H.

inversion H.
inversion H0.
apply appears_minus with a.
apply H2.
apply ai_here.

inversion H.
apply appears_diff with l2.
apply H0.
apply ai_here.
Qed.

Theorem appears_more : forall {X : Type} (l : list X) (a b : X),
	appears_in a l -> appears_in a (b :: l).
Proof.
intros X.
intros l a b.
intros H.
apply ai_later.
apply H.
Qed.

Theorem disjoint_less : forall {X : Type} (l1 l2 : list X) (a : X),
	disjoint (a :: l1) l2 -> disjoint l1 l2.
Proof.
intros X.
intros l1 l2 a.
intros H.
inversion H.
unfold disjoint.
split.
intros a0.
intros H2.
apply H0.
apply appears_more.
apply H2.

intros a0.
intros H2.
apply appears_minus with a.
apply H1.
apply H2.
Qed.

Theorem no_exists_disjoint : forall {X : Type} (l1 l2 : list X) (x : X),
 ~(appears_in x l1) -> disjoint (x :: l1) l2 -> ~(appears_in x (l1 ++ l2)).
Proof.
intros X l1 l2 x.
intros H1.
intros H2.
apply no_appears_app.
apply H1.
  
assert (disjoint l1 l2).
apply disjoint_less in H2.
apply H2.
			  
inversion H2.
apply H0.
apply ai_here.
Qed.

Theorem repeats_disjoint: forall {X:Type} (l1 l2 : list X),
 no_repeats l1 -> no_repeats l2 ->
 disjoint l1 l2 -> no_repeats (l1 ++ l2).
Proof.
 intros X.
 induction l1.
 intros l2.
 intros H.
 intros H1.
 intros H2.
 apply H1.
 simpl.
 intros l2.
 intros H1.
 intros H2.
 intros H3.
 apply repeats_in.
 apply IHl1.
 inversion H1.
					    apply H4.
							   
							   apply H2.
apply disjoint_add in H3.
   apply H3.
	 inversion H1.
	   apply no_exists_disjoint.
		    apply H5.
				   
				   apply H3.
Qed.

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
	| all_base : all X P []
	| all_inc : forall (l : list X) (x : X), P x -> all X P l -> all X P (x :: l).

Theorem forallb_ok : forall {X:Type} (l : list X) (f : X -> bool),
	all X (fun x => f x = true) l <-> forallb f l = true.
Proof.
intros X.
induction l.
intros f.
unfold iff.
split.
intros H.
simpl.
reflexivity.

intros H.
apply all_base.

intros f.
unfold iff.
split.
intros H.
simpl.
inversion H.
destruct (f x).
simpl.
unfold iff in IHl.
   assert
	     (forall f : X -> bool,
				     all X (fun x : X => f x = true) l -> forallb f l = true).
			     intros f0.
					     intros H4.
							     apply IHl in H4.
									     apply H4.
											     
											     apply H4.

apply H3.

inversion H2.

simpl.
intros H.
apply all_inc.
destruct (f x).
reflexivity.

simpl in H.
inversion H.

unfold iff in IHl.
   assert
	     (forall f : X -> bool,
				     forallb f l = true -> all X (fun x : X => f x = true) l).
			     intros f0.
					     intros H1.
							     apply IHl in H1.
									     apply H1.

destruct (f x).
simpl in H.
apply H0.
apply H.

simpl in H.
inversion H.
Qed.

Theorem O_le_n : forall n,
	O <= n.
Proof.
induction n.
apply le_n.

apply le_S.
apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
	n <= m -> S n <= S m.
Proof.
destruct n.
induction m.
intros H.
apply le_n.

intros H.
apply le_S.
apply IHm.
apply O_le_n.

induction m.
intros H.
inversion H.

intros H.
inversion H.
apply le_n.

apply le_S.
apply IHm.
apply H1.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
	S n <= S m -> n <= m.
Proof.
	intros n m.
	generalize dependent n.
	induction m.
	intros n.
	intros H.
	destruct n.
	apply le_n.

	inversion H.
	inversion H1.
	intros n.
	destruct n.
	simpl.
	intros H.
	apply O_le_n.

	intros H.
	inversion H.
	apply le_n.

	simpl.
	subst.
	assert (S n <= m).
	apply IHm in H1.
	apply H1.

	apply le_S.
	apply H0.
Qed.

Theorem le_plus_1 : forall a b,
		a <= a + b.
Proof.
intros a.
intros b.
generalize dependent a.
induction b.
simpl.
intros a.
simpl.
rewrite plus_0_r.
apply le_n.

intros a.
rewrite <- plus_n_Sm.
apply le_S.
apply IHb.
Qed.

Theorem le_less_one : forall n1 n2,
	S n1 <= n2 -> n1 <= n2.
Proof.
induction n1.
intros n2.
intros H.
apply O_le_n.

intros n2.
intros H.
destruct n2.
inversion H.

apply n_le_m__Sn_le_Sm.
apply IHn1.
apply Sn_le_Sm__n_le_m in H.
apply H.
Qed.

Theorem plus_lt : forall n1 n2 m,
	n1 + n2 < m ->
		n1 < m /\ n2 < m.
Proof.
induction n1.
intros n2.
simpl.
intros m.
split.
unfold lt.
destruct m.
unfold lt in H.
inversion H.

simpl.
unfold lt in H.
apply n_le_m__Sn_le_Sm.
apply O_le_n.

apply H.

intros n2 m.
intros H.
destruct m.
inversion H.

split.
apply Sn_le_Sm__n_le_m in H.
unfold lt.
unfold lt in H.
unfold lt in IHn1.
apply n_le_m__Sn_le_Sm.
simpl in H.
apply IHn1 in H.
inversion H.
apply H0.


destruct n2.
simpl in H.
rewrite plus_0_r in H.
unfold lt.
apply n_le_m__Sn_le_Sm.
apply O_le_n.

apply n_le_m__Sn_le_Sm.
destruct m.
inversion H.
inversion H1.
simpl in H.
assert (forall n2 m, n1 + n2 < m -> n2 < m).
intros n3 m0.
intros H1.
apply IHn1 in H1.
inversion H1.
apply H2.

apply H0.
rewrite <- plus_n_Sm in H.
simpl in H.
unfold lt in |- *.
unfold lt in H.
apply Sn_le_Sm__n_le_m in H.
apply le_less_one in H.
apply H.
Qed.

Theorem lt_S : forall n m,
	n < m ->
		n < S m.
Proof.
induction n.
intros m.
intros H.
unfold lt.
unfold lt in H.
apply n_le_m__Sn_le_Sm.
apply O_le_n.

intros m.
unfold lt.
intros H.
unfold lt in IHn.
destruct m.
inversion H.

apply n_le_m__Sn_le_Sm.
apply le_less_one in H.
apply H.
Qed.									   

Theorem ble_nat_true : forall n m,
	ble_nat n m = true -> n <= m.
Proof.
induction n.
intros m.
simpl.
intros H.
apply O_le_n.

intros m.
simpl.
destruct m.
intros H.
inversion H.

intros H.
apply n_le_m__Sn_le_Sm.
apply IHn.
apply H.
Qed.

Theorem ble_nat_n_Sn_false : forall n m,
	ble_nat n (S m) = false ->
		ble_nat n m = false.
Proof.
induction n.
intros m.
simpl.
intros H.
inversion H.

intros m.
simpl.
destruct m.
simpl.
intros H.
reflexivity.

intros H.
apply IHn.
apply H.
Qed.

Theorem ble_nat_false : forall n m,
	ble_nat n m = false -> ~(n <= m).
Proof.
intros n m.
generalize dependent n.
induction m.
intros n.
simpl.
intros H.
destruct n.
simpl in H.
inversion H.

simpl in H.
intros H1.
inversion H1.

destruct n.
intros H.
simpl.
simpl in H.
inversion H.

simpl.
intros H.
simpl.
intros H1.
apply Sn_le_Sm__n_le_m in H1.
unfold not in IHm.
apply IHm with n.
apply H.

apply H1.
Qed.

Lemma app_length : forall {X:Type} (l1 l2 : list X),
	length (l1 ++ l2) = length l1 + length l2.
Proof.
intros X.
induction l1.
simpl.
intros l2.
auto.

simpl.
intros l2.
assert (forall n1 n2, n1 = n2 -> S n1 = S n2).
intros n1 n2.
intros H1.
rewrite H1.
reflexivity.

apply H.
apply IHl1.
Qed.

Lemma appears_in_app_split : forall {X:Type} (x:X) (l:list X),
	appears_in x l ->
		exists l1, exists l2, l = l1 ++ (x :: l2).
Proof.
intros X.
intros x.
intros l.
generalize dependent x.
induction l.
intros x.
intros H.
inversion H.

intros x0.
intros H.
inversion H.
simpl.
subst.
exists [].
simpl.
exists l.
reflexivity.

subst.
apply IHl in H1.
inversion H1.
inversion H0.
exists (x :: witness).
simpl.
exists witness0.
rewrite H2.
reflexivity.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
	| repeats_new : forall l x, appears_in x l -> repeats (x::l)
	| repeats_more : forall l x, repeats l -> repeats (x::l).

Example repeats1 :
	repeats [S O, O, S O].
Proof.
apply repeats_new.
apply ai_later.
apply ai_here.
Qed.

Example repeats2 :
	~(repeats [true, false]).
Proof.
intros H.
inversion H.
subst.
inversion H1.
subst.
inversion H2.

subst.
inversion H1.
subst.
inversion H2.

subst.
inversion H2.
Qed.

Theorem le_or : forall (a b : nat),
	a <= b -> a < b \/ a = b.
Proof.
induction a.
intros b.
intros H1.
unfold lt.
inversion H1.
right.
reflexivity.

subst.
left.
apply n_le_m__Sn_le_Sm in H.
apply H.

simpl.
unfold lt.
intros b.
intros H1.
destruct b.
left.
inversion H1.

inversion H1.
right.
reflexivity.

subst.
left.
apply n_le_m__Sn_le_Sm in H0.
apply H0.
Qed.

Theorem le_O : forall (a : nat),
	a <= O -> a = O.
Proof.
destruct a.
intros H.
reflexivity.

intros H.
inversion H.
Qed.

Theorem le_O_or_1 : forall (a : nat),
	a <= S O -> a = O \/ a = (S O).
Proof.
destruct a.
intros H.
left.
reflexivity.

intros H.
apply Sn_le_Sm__n_le_m in H.
apply le_O in H.
right.
rewrite H.
reflexivity.
Qed.

Theorem le_imp : forall (a : nat),
	~ (S (S a) <= a).
Proof.
induction a.
intros H.
inversion H.

intros H.
apply Sn_le_Sm__n_le_m in H.
generalize dependent H.
unfold not in IHa.
apply IHa.
Qed.

Theorem contra_le : forall (a b : nat),
	a < b -> ~(b < a).
Proof.
induction a.
intros b H1.
intros H2.
unfold lt in H2.
unfold lt in H1.
inversion H2.

intros b.
intros H1.
intros H2.
unfold not in IHa.
apply IHa with b.
apply le_less_one in H1.
unfold lt.
apply H1.

unfold lt.
unfold lt in H1.
unfold lt in H2.
apply Sn_le_Sm__n_le_m in H2.
apply le_or in H2.
inversion H2.
unfold lt in H.
apply H.

rewrite H in H1.
rewrite H.
apply le_imp in H1.
inversion H1.
Qed.


Theorem pige1 : forall {X:Type} (l1 l2 : list X) (x : X),
	(forall x0, appears_in x0 (x :: l1) -> appears_in x0 l2) ->
		length l1 <= S (length l2).
Proof.
intros X.
induction l1.
simpl.
intros l2 x H1.
apply O_le_n.

simpl.
intros l2 x0 H.
assert
((forall x1 : X, appears_in x1 (x0 :: x :: l1) -> appears_in x1 l2) ->
 forall x1 : X, appears_in x1 (x :: l1) -> appears_in x0 l2).
intros H1.
intros x1.
intros H2.
apply H1.
apply ai_here.

assert
((forall x1 : X, appears_in x1 (x0 :: x :: l1) -> appears_in x1 l2) ->
 forall x1 : X, appears_in x1 (x :: l1) -> appears_in x1 l2).
intros H1.
intros x1.
intros H2.
apply H1.
apply ai_later.
apply H2.

apply IHl1 in H1.
apply n_le_m__Sn_le_Sm.
admit.

apply H.
Qed.

													(*
Theorem pigeonhole_principle : forall {X:Type} (l1 l2 : list X),
	excluded_middle ->
		(forall x, appears_in x l1 -> appears_in x l2) ->
		length l2 < length l1 ->
			repeats l1.
Proof.
	intros X l1.
	induction l1.
	intros l2 H.
	intros H1.
	destruct l2.
	simpl.
	intros H2.
	inversion H2.

	intros H2.
	inversion H2.

	intros l2.
	intros H1.
	unfold excluded_middle in H1.
	intros H2.
	intros H3.
	unfold lt in H3.
	simpl in H3.
	apply repeats_more.
	apply IHl1 with l2.
	unfold excluded_middle.
	apply H1.

	intros x0.
	intros H4.
	apply H2.
	apply appears_more.
	apply H4.

	unfold lt.
	apply pige1 in H2.
	apply le_less_one in H3.
	apply contra_le in H2.
	inversion H2.

	apply contra_le in H3.
	inversion H3.

	apply H2.
Qed.


Definition nat_ind2 :
	forall (P : nat -> Prop),
		P O ->
		P (S O) ->
			(forall n : nat, P n -> P (S (S n))) ->
			forall n : nat, P n :=
			fun P => fun P0 => fun P1 => fun PSS =>
				fix f (n:nat) := match n return P n with
												 O => P0
												 | S O => P1
												 | S (S n') => PSS n' (f n')
											end.

Lemma even_ev' : forall n, even n -> ev n.
Proof.
	intros.
	induction n as [ | | n'] using nat_ind2.
	Case "even 0".
		apply ev_0.
	Case "even 1".
		inversion H.
	Case "even (S (S n'))".
		apply ev_SS.
		apply IHn'. unfold even. unfold even in H. simpl in H. apply H.
Qed.
*)
