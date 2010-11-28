Require Export Poly.
Require Export Lists.

Import Playground1.

Definition even (n:nat) :=
	evenb n = true.

Inductive good_day : day -> Prop :=
	| gd_sat : good_day saturday
	| gd_sun : good_day sunday.

Theorem gds : good_day sunday.
Proof. apply gd_sun. Qed.

Inductive day_before : day -> day -> Prop :=
	| db_tue : day_before tuesday monday
	| db_wed : day_before wednesday tuesday
	| db_thu : day_before thursday wednesday
	| db_fri : day_before friday thursday
	| db_sat : day_before saturday friday
	| db_sun : day_before sunday saturday
	| db_mon : day_before monday sunday.

Inductive fine_day_for_singing : day -> Prop :=
	| fdfs_any : forall d:day, fine_day_for_singing d.

Theorem fdfs_wed : fine_day_for_singing wednesday.
Proof. apply fdfs_any. Qed.

Definition fdfs_wed' : fine_day_for_singing wednesday :=
	fdfs_any wednesday.

Inductive ok_day : day -> Prop :=
	| okd_gd : forall d, good_day d -> ok_day d
	| okd_before : forall d1 d2, ok_day d2 -> day_before d2 d1 -> ok_day d1.

Definition okdw : ok_day wednesday :=
	okd_before wednesday thursday
		(okd_before thursday friday
		 	(okd_before friday saturday
			 	(okd_gd saturday gd_sat)
				db_sat)
			db_fri)
		db_thu.

Theorem okdw' : ok_day wednesday.
Proof.
(* wednesday is OK because it's the day before an OK day *)
apply okd_before with (d2:=thursday).
(* "subgoal: show that thursday is ok". *)
(* thursday is OK because it's the day before an OK day *)
apply okd_before with (d2:=friday).
(* "subgoal: show that friday is ok". *)
(* friday is OK because it's the day before an OK day *)
apply okd_before with (d2:=saturday).
(* "subgoal: show that saturday is ok". *)
(* saturday is OK because it's good! *)
apply okd_gd. apply gd_sat.
(* "subgoal: show that the day before saturday is friday". *)
apply db_sat.
(* "subgoal: show that the day before friday is thursday". *)
apply db_fri.
(* "subgoal: show that the day before thursday is wednesday". *)
apply db_thu. Qed.

Definition okd_before2 := forall d1 d2 d3,
	ok_day d3 ->
		day_before d2 d1 ->
			day_before d3 d2 ->
				ok_day d1.


Theorem okd_before2_valid : okd_before2.
Proof.
	intros d1 d2 d3.
	intros eq1 eq2 eq3.
	apply okd_before with (d2 := d2).
	apply okd_before with (d2 := d3).
 	apply eq1.
  apply eq3.
	apply eq2.
Qed.

Definition okd_before2_valid' : okd_before2 :=
	fun (d1 d2 d3 : day) =>
		fun (H : ok_day d3) =>
			fun (H0 : day_before d2 d1) =>
				fun (H1 : day_before d3 d2) =>
					okd_before d1 d2 (okd_before d2 d3 H H1) H0.

Theorem mult_0_r' : forall n:nat,
	n * O = O.
Proof.
	apply nat_ind.
	Case "O". reflexivity.
	Case "S". simpl. intros n IHn. rewrite -> IHn.
	reflexivity. Qed.

Theorem plus_one_r' : forall n : nat,
		n + (S O) = S n.
Proof.
apply nat_ind.
simpl.
reflexivity.

simpl.
intros n.
intros IHn.
rewrite IHn.
reflexivity.
Qed.

Inductive rgb : Type :=
	| red : rgb
	| green : rgb
	| blue : rgb.

Inductive natlist1 : Type :=
	| nnil1 : natlist1
	| nsnoc1 : natlist1 -> nat -> natlist1.

Inductive ExSet : Type :=
	| con1 : bool -> ExSet
	| con2 : nat -> ExSet -> ExSet.

Inductive tree (X:Type) : Type :=
	| leaf : X -> tree X
	| node : tree X -> tree X -> tree X.

Inductive mytype (X:Type) : Type :=
	| constr1 : X -> mytype X
	| constr2 : nat -> mytype X
	| constr3 : mytype X -> nat -> mytype X.
	
Inductive foo (X Y : Type) : Type :=
	| bar : X -> foo X Y
	| baz : Y -> foo X Y
	| quux : (nat -> foo X Y) -> foo X Y.

Inductive foo' (X : Type) : Type :=
	| C1 : list X -> foo' X -> foo' X
	| C2 : foo' X.

Theorem plus_assoc'' : forall m p n : nat,
		n + (m + p) = (n + m) + p.
Proof.
intros m p.
apply nat_ind.
reflexivity.

intros n eq.
simpl.
rewrite eq.
reflexivity.
Qed.

Theorem plus_comm'' : forall m n : nat,
	n + m = m + n.
Proof.
intros m.
apply nat_ind.
simpl.
rewrite plus_0_r.
reflexivity.

intros n eq.
simpl.
rewrite eq.
rewrite <- plus_n_Sm.
reflexivity.
Qed.

Fixpoint true_upto_n__true_everywhere (n : nat) (f : nat -> Prop) : Prop :=
	match n with
		| O => forall m : nat, f m
		| S n' => (f n) -> true_upto_n__true_everywhere n' f
	end.

Example true_upto_n_example : (true_upto_n__true_everywhere (S (S (S O))) (fun n => even n)) = (even (S (S (S O))) -> even (S (S O)) -> even (S O) -> forall m : nat, even m).
Proof. reflexivity. Qed.

Inductive ev : nat -> Prop :=
	| ev_0 : ev O
	| ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem four_even:
	ev (S (S (S (S O)))).
Proof.
apply ev_SS.
apply ev_SS.
apply ev_0.
Qed.

Theorem even_n_4n : forall (n : nat),
				ev n -> ev ((S (S (S (S O)))) + n).
Proof.
intros n.
induction n.
simpl.
intros eq.
apply four_even.
simpl.
intros eq.
apply ev_SS.
apply ev_SS.
apply eq.
Qed.

Theorem double_even : forall n,
				(ev (double n)).
Proof.
intros n.
simpl.
induction n.
simpl.
apply ev_0.
simpl.
apply ev_SS.
apply IHn.
Qed.

Theorem ev_minus2: forall n,
	ev n -> ev (pred (pred n)).
Proof.
	intros n E.
	destruct E.
	simpl. apply ev_0.
	simpl. apply E. Qed.

Theorem ev_even: forall n,
	ev n -> even n.
Proof.
	intros n E. induction E as [| n' E'].
 	Case "E = ev_0".
		unfold even. reflexivity.
	Case "E = ev_SS n' E'".
		unfold even. simpl. unfold even in IHE'. apply IHE'. Qed.

Theorem ev_sum : forall n m,
	ev n -> ev m -> ev (n + m).
Proof.
	intros n m E.
	induction E.
 simpl.
	intros eq.
	 apply eq.
		  
	simpl.
	intros eq.
	apply ev_SS.
	apply IHE.
	apply eq.
	Qed.

Theorem SSev_even : forall n,
	ev (S (S n)) -> ev n.
Proof.
	intros n E.
	inversion E.
	apply H0.
	Qed.

Theorem SSSSev_even : forall n,
	ev (S (S (S (S n)))) -> ev n.
Proof.
	intros n E.
	inversion E.
	inversion H0.
	apply H2.
	Qed.

Theorem even5_nonsense :
	ev (S (S (S (S (S O))))) -> (S (S O)) + (S (S O)) = (S (S (S O))).
Proof.
intros eq.
inversion eq.
inversion H0.
inversion H2.
Qed.

Theorem ev_minus2': forall n,
	ev n -> ev (pred (pred n)).
Proof.
	intros n E. inversion E.
 	apply ev_0.
	apply H.
	Qed.

Theorem ev_ev_even : forall n m,
	ev (n + m) -> ev n -> ev m.
Proof.
intros n m eq1 eq2.
induction eq2.
simpl in eq1.
apply eq1.
	 
simpl in eq1.
inversion eq1.
apply IHeq2.
apply H0.
Qed.

Theorem ev_plus_plus : forall n m p,
	ev (n + m) -> ev ( n + p ) -> ev (m + p).
Proof.
intros n m p.
intros eq1.
assert (m + p = p + m) as H.
rewrite plus_comm.
reflexivity.

rewrite H.
apply ev_ev_even.
assert (n + p = p + n) as H1.
rewrite plus_comm.
reflexivity.

rewrite H1.
assert (n + (p + m) = p + (n + m)) as H2.
rewrite plus_swap.
reflexivity.

rewrite plus_assoc.
rewrite <- plus_assoc.
rewrite <- plus_assoc.
rewrite H2.
rewrite plus_assoc.
apply ev_sum.
rewrite <- double_plus.
apply double_even.

apply eq1.
Qed.

Inductive MyProp : nat -> Prop :=
	| MyProp1 : MyProp (S (S (S (S O))))
	| MyProp2 : forall n:nat, MyProp n -> MyProp ((S (S (S (S O)))) + n)
	| MyProp3 : forall n:nat, MyProp ((S (S O)) + n) -> MyProp n.



Theorem MyProp_ten : MyProp (S (S (S (S (S (S (S (S (S (S O)))))))))).
Proof.
	apply MyProp3. simpl.
	assert((S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))) = (S (S (S (S O)))) + (S (S (S (S (S (S (S (S O))))))))) as H12.
		reflexivity.
	rewrite -> H12.
	apply MyProp2.
	assert((S (S (S (S (S (S (S (S O)))))))) = (S (S (S (S O)))) + (S (S (S (S O))))) as H8.
		reflexivity.
	rewrite -> H8.
	apply MyProp2.
	apply MyProp1. Qed.

Theorem MyProp_0 : MyProp O.
Proof.
	apply MyProp3.
	simpl.
	apply MyProp3.
	simpl.
	apply MyProp1.
Qed.

Theorem MyProp_plustwo : forall n:nat, MyProp n -> MyProp (S (S n)).
Proof.
	intros n.
	intros eq.
	apply MyProp3.
	simpl.
	apply MyProp2 in eq.
	simpl in eq.
	apply eq.
Qed.

Theorem ev_MyProp : forall n : nat,
	MyProp n -> ev n.
Proof.
intros n E.
induction E.
simpl.
apply ev_SS.
apply ev_SS.
apply ev_0.

simpl.
apply ev_SS.
apply ev_SS.
apply IHE.

simpl IHE.
simpl in IHE.
simpl in E.
apply SSev_even.
apply IHE.
Qed.

Theorem ev_MyProp' : forall n : nat,
					MyProp n -> ev n.
Proof.
intros n E.
apply MyProp_ind.
simpl.
apply ev_SS.
apply ev_SS.
apply ev_0.

intros n0.
intros eq.
intros eq2.
simpl.
apply ev_SS.
apply ev_SS.
apply eq2.

intros n0.
intros eq1.
simpl in eq1.
simpl.
intros eq2.
apply ev_minus2 in eq2.
simpl in eq2.
apply eq2.

apply E.
Qed.

Inductive p : (tree nat) -> nat -> Prop :=
	| c1 : forall n, p (leaf _ n) (S O)
	| c2 : forall t1 t2 n1 n2,
					p t1 n1 -> p t2 n2 -> p (node _ t1 t2) (n1 + n2)
	| c3 : forall t n, p t n -> p t (S n).

Theorem double_injective_take2 : forall n m,
	double n = double m ->
	n = m.
Proof.
	intros n m.
	generalize dependent n.
	induction m as [| m'].
	Case "m = O". simpl. intros n eq. destruct n as [| n'].
			SCase "n = O". reflexivity.
			SCase "n = S n'". inversion eq.
	Case "m = S m'". intros n eq. destruct n as [| n'].
		SCase "n = O". inversion eq.
		SCase "n = S n'".
			assert(n' = m') as H.
			SSCase "Proof by assertion".
				apply IHm'. inversion eq. reflexivity.
			rewrite -> H. reflexivity. Qed.

Theorem plus_n_n_injective_take2 : forall n m,
		n + n = m + m ->
			n = m.
Proof.
	intros n m.
	generalize dependent n.
	induction m.
	simpl.
	destruct n.
	reflexivity.

	intros eq.
	inversion eq.

	destruct n.
	simpl.
	intros eq.
	inversion eq.

	simpl.
	rewrite <- plus_distr.
	rewrite <- plus_distr.
	simpl.
	intros eq1.
	inversion eq1.
	apply IHm in H0.
	simpl.
	rewrite H0.
	reflexivity.
Qed.

Theorem index_after_last : forall (n : nat) (X : Type)
	(l : list X),
		length l = n ->
			index _ (S n) l = None.
Proof.
	intros n X l.
	generalize dependent n.
	induction l.
	simpl.
	reflexivity.

	simpl.
	intros n.
	intros eq.
	destruct n.
	simpl.
	inversion eq.

	inversion eq.
	apply IHl.
	reflexivity.
Qed.

Theorem length_snoc''' : forall (n : nat) (X : Type)
											(v : X) (l : list X),
	length l = n ->
		length (snoc l v) = S n.
Proof.
	intros n X v l.
	generalize dependent n.
	induction l.
	simpl.
	intros n.
	intros eq.
	rewrite eq.
	reflexivity.

	simpl.
	intros n.
	destruct n.
	simpl.
	intros eq.
	inversion eq.

	intros eq.
	simpl.
	inversion eq.
	apply IHl in H0.
	simpl.
	rewrite H0.
	inversion eq.
	rewrite H1.
	reflexivity.
Qed.

Theorem eqnat_false_S : forall n m,
	beq_nat n m = false -> beq_nat (S n) (S m) = false.
Proof.
	intros n m.
	generalize dependent n.
	induction m.
	simpl.
	intros n eq.
	apply eq.

	intros n.
	simpl.
	intros eq.
	apply eq.
Qed.

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) (x : X) (n : nat),
			length (l1 ++ (x :: l2)) = n ->
					S (length (l1 ++ l2)) = n.
Proof.
intros X l1 l2 x n.
generalize dependent n.
generalize dependent l2.
induction l1.
simpl.
induction l2.
simpl.
intros n eq.
apply eq.

simpl.
intros n.
intros eq.
apply eq.

induction l2.
intros n.
simpl.
intros eq.
inversion eq.
destruct n.
inversion eq.

simpl.
inversion H.
apply IHl1 in H1.
simpl.
rewrite H.
rewrite H1.
reflexivity.

intros n.
simpl.
intros eq.
destruct n.
simpl.
inversion eq.

inversion eq.
apply IHl1 in H0.
rewrite eq.
rewrite H0.
reflexivity.
Qed.

Theorem nat_simpl : forall (n m : nat),
		n = m -> S n = S m.
Proof.
	intros n m eq.
	rewrite -> eq.
	reflexivity.
	Qed.

Theorem app_cons_2: forall (X:Type) (l1 l2 : list X) (x : X) (n : nat),
	S (length (l1 ++ l2)) = n ->
		length (l1 ++ (x :: l2)) = n.
Proof.
intros X l1 l2 x n.
generalize dependent n.
generalize dependent l2.
induction l1.
simpl.
intros l2 n.
intros eq.
apply eq.

simpl.
intros l2 n.
intros eq.
destruct n.
simpl.
inversion eq.

inversion eq.
apply IHl1 in H0.
rewrite H0.
rewrite eq.
reflexivity.
Qed.


Theorem app_length_twice : forall (X:Type) (n:nat)
	(l : list X),
	length l = n ->
	length (l ++ l) = n + n.
	Proof.
	intros X n l.
	generalize dependent n.
	induction l.
	simpl.
	intros n.
	intros eq.
	rewrite eq.
	rewrite <- eq.
	reflexivity.

	simpl.
	intros n.
	destruct n.
	simpl.
	intros eq.
	inversion eq.

	simpl.
	intros eq.
	inversion eq.
	simpl.
	apply IHl in H0.
	simpl.
	rewrite eq.
	simpl.
	inversion eq.
	rewrite H1.
	simpl.
	rewrite <- plus_distr.
	apply nat_simpl.
	apply app_cons_2.
	simpl.
	apply nat_simpl.
	apply IHl.
	apply H1.
Qed.

Inductive pal : list nat -> Prop :=
	| pal_base : pal []
	| pal_one : forall n:nat, pal [n]
	| pal_i : forall (n : nat) (l : list nat), pal l -> pal (n :: l ++ [n]).

Theorem snoc_append : forall (l : list nat) (n : nat),
	snoc l n = l ++ [n].
Proof.
	intros l n.
	induction l.
	Case "l = nil".
		reflexivity.
	Case "l = cons".
		simpl.
		rewrite -> IHl.
		reflexivity.
		Qed.

Theorem app_ass : forall l1 l2 l3 : list nat,
	(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
	intros l1. induction l1 as [ | n l1'].
	reflexivity.
	simpl.
	intros l2 l3.
	rewrite -> IHl1'.
	reflexivity.
	Qed.

Theorem pal_plus_rev : forall (l : list nat),
	pal (l ++ rev l).
Proof.
	intros l.
	induction l.
	simpl. apply pal_base.
	simpl. rewrite -> snoc_append.
	rewrite <- app_ass.
  apply pal_i.
	apply IHl.
Qed.

Theorem rev_snoc : forall l: list nat, forall n : nat,
	rev (snoc l n) = n :: (rev l).
Proof.
	intros l n.
	induction l.
	Case "l = nil".
		reflexivity.
	Case "l = cons".
		simpl.
		rewrite -> IHl.
		reflexivity.
		Qed.

Theorem pal_rev : forall (l : list nat),
		pal l -> l = rev l.
Proof.
intros l.
intros eq.
induction eq.
simpl.
reflexivity.

simpl.
reflexivity.

simpl.
rewrite snoc_append.
rewrite <- snoc_append.
rewrite rev_snoc.
simpl.
rewrite <- IHeq.
rewrite snoc_append.
reflexivity.
Qed.

Theorem todo: forall (l c: list nat) (n : nat),
		n :: c = rev l -> n :: l = n :: c ++ [n] -> pal c.
Proof.
Admitted.
	
Theorem rev_pal : forall (l : list nat),
		l = rev l -> pal l.
Proof.

intros l.
intros eq.
rewrite eq.
induction l.
 simpl.
  apply pal_base.
	 
	 simpl.
	  simpl in eq.
		 remember (rev l) as c.
		  destruct c.
			  simpl.
				  apply pal_one.
					  
					  simpl.
						  rewrite snoc_append.
							  simpl in eq.
								  rewrite snoc_append in eq.
									inversion eq.
									rewrite H0 in eq.
												 apply pal_i.

	assert (n :: c = rev l -> n :: l = n :: c ++ [n] -> pal c) as H2.
	apply todo.
	     
	    apply H2.
	      apply Heqc.
		     
		     apply eq.
Qed.

Inductive subseq : list nat -> list nat -> Prop :=
	| subseq_base : forall (l : list nat), subseq [] l
	| subseq_one : forall (n : nat) (l a: list nat), subseq a l -> subseq (n :: a) (n :: l)
	| subseq_i : forall (n: nat) (l a : list nat), subseq a l -> subseq a (n :: l).

Theorem subseq_refl : forall (l: list nat),
	subseq l l.
Proof.
intros l.
induction l.
 apply subseq_base.
  
  apply subseq_one.
	 apply IHl.
Qed.

Theorem app_nil_end : forall l : list nat,
	l ++ [] = l.
Proof.
	intros l.
	induction l.
	Case "l = nil".
		reflexivity.
	Case "l = cons".
		simpl. rewrite -> IHl. reflexivity. Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
	subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
intros l1 l2 l3.
generalize dependent l1.
generalize dependent l2.
induction l3.
simpl.
intros l2 l1.
intros eq.
rewrite -> app_nil_end.

apply eq.

simpl.
induction l2.
simpl.
induction l1.
simpl.
intros eq.
apply subseq_base.

simpl.
intros eq.
inversion eq.

simpl.
intros l1.
simpl.
simpl.
induction l1.
simpl.
intros eq.
apply subseq_base.

simpl.
intros eq.
inversion eq.
apply subseq_one.
simpl.
apply IHl2.
apply H0.

apply subseq_i.
apply IHl2.
apply H1.
Qed.

(*
Theorem subseq_transitive : forall (l1 l2 l3: list nat),
		subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
TODO: XXX
*)

Inductive foo2 (X : Set) (Y : Set) : Set :=
	| foo12 : X -> foo2 X Y
	| foo22 : Y -> foo2 X Y
	| foo32 : foo2 X Y -> foo2 X Y.

Inductive bar2: Set :=
	| bar12: nat -> bar2 
	| bar22: bar2 -> bar2
	| bar33: bool -> bar2 -> bar2.

Inductive no_longer_than (X : Set) : (list X) -> nat -> Prop :=
	| nlt_nil : forall n, no_longer_than X [] n
	| nlt_cons : forall x l n, no_longer_than X l n -> 
														no_longer_than X (x::l) (S n)
	| nlt_succ : forall l n, no_longer_than X l n -> 
										no_longer_than X l (S n).

Inductive R : nat -> list nat -> Prop :=
	| Rc1 : R O []
	| Rc2 : forall n l, R n l -> R (S n) (n :: l)
	| Rc3 : forall n l, R (S n) l -> R n l.

