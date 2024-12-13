From Coq Require Import Lists.List.
From Coq Require Import Lists.ListSet.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Unicode.Utf8.

Module Paxos.

Inductive node : Type :=
    | nodeID : nat -> node.

Inductive value : Type :=
    | valueID : nat -> value.

Inductive number : Type :=
    | numberID : nat -> number.

Definition beq_node (n1 n2 : node) :=
    match n1, n2 with
    | nodeID n1, nodeID n2 => n1 =? n2
    end.

Definition beq_value (v1 v2 : value) :=
    match v1, v2 with
    | valueID n1, valueID n2 => n1 =? n2
    end.

Theorem beq_value_true : ∀ (v1 v2 : value),
    beq_value v1 v2 = true → v1 = v2.
Proof. intros. destruct v1. induction v2.
    generalize dependent n0. induction n.
    { destruct n0.
        { reflexivity. }
        { intros. inversion H. } }
    {destruct n0.
        { intros H. inversion H. }
        { intros H. simpl in IHn. apply IHn in H. inversion H. reflexivity. } }
Qed.

Theorem beq_value_refl : ∀ v : value,
    beq_value v v = true.
Proof.
    intros. destruct v. induction n.
    { simpl. reflexivity. }
    { apply IHn. }
Qed.

Theorem beq_value_true_iff : ∀ (v1 v2 : value),
    beq_value v1 v2 = true <-> v1 = v2.
Proof. split.
    { apply beq_value_true. }
    { intros H. rewrite H. apply beq_value_refl. }
Qed.

Definition blt_value (v1 v2 : value) :=
    match v1, v2 with
    | valueID v1, valueID v2 => v1 <? v2
    end.

Definition beq_number (x1 x2 : number) :=
    match x1, x2 with
    | numberID n1, numberID n2 => n1 =? n2
    end.

Definition blt_number (x1 x2 : number) :=
    match x1, x2 with
    | numberID n1, numberID n2 => n1 <? n2
    end.

Definition leq_number (x1 x2 : number) := beq_number x1 x2 = true \/ blt_number x1 x2 = true.

Theorem beq_number_true : ∀ n1 n2 : number,
    beq_number n1 n2 = true -> n1 = n2.
Proof.
    intros. destruct n1. induction n2. generalize dependent n0. induction n.
    { destruct n0.
        { reflexivity. }
        { intros H. inversion H. } }
    { intros n0. destruct n0.
        { intros H. inversion H. }
        { intros H. apply IHn in H. inversion H. reflexivity. } }
Qed.

(* TODO: Homogenize this with `beq_value_refl` *)
Theorem beq_number_refl : ∀ x : number, beq_number x x = true.
Proof.
    intros. destruct x. induction n.
        { simpl. reflexivity. }
        { apply IHn. }
Qed.

Theorem beq_number_true_iff : ∀ x1 x2 : number,
    beq_number x1 x2 = true <-> x1 = x2.
Proof.
    split.
    { apply beq_number_true. }
    { intros H. rewrite H. apply beq_number_refl. }
Qed.

Axiom Aeq_dec : ∀ (n1 n2 : node), {n1 = n2} + {n1 <> n2}.

(********* Quora *********)
Definition quorum : Type := set node.
Definition empty_quorum : quorum := empty_set node.
Parameter quora : set (quorum).

Notation "a '∈' b" := (set_In a b) (at level 70, no associativity).

Theorem quora_double : ∀ (q1 q2 : quorum),
    q1 ∈ quora -> q2 ∈ quora -> q1 ∈ quora ∧ q2 ∈ quora.
Proof.
    intros. split. assumption. assumption.
Qed.

Theorem empty_spec : ∀ (x : node),
    ~(x ∈ empty_quorum).
Proof.
    intros. unfold empty_quorum. unfold empty_set. unfold not. intros H. inversion H.
Qed.

Theorem empty_spec_iff : ∀ (x : node),
    x ∈ empty_quorum <-> False.
Proof.
    intros. split.
    { apply empty_spec. }
    { intros. inversion H. }
Qed.

Theorem empty_spec_mem : ∀ (q : quorum),
    (∃ x, set_mem Aeq_dec x q = true) -> q <> empty_quorum.
Proof.
    intros. inversion H. apply set_mem_correct1 in H0.
    unfold not. intros H1. rewrite H1 in H0.
    apply empty_spec_iff in H0. apply H0.
Qed.

(* Quora have at least one node in common *)
(* Existence corollary *)
Axiom quora_assumption_existence : ∀ (q1 q2 : quorum),
    q1 ∈ quora ∧ q2 ∈ quora -> ∃ (n : node), n ∈ (set_inter Aeq_dec q1 q2).

Theorem quorum_nonempty_a : ∀ (q1 q2 : quorum),
    q1 ∈ quora ∧ q2 ∈ quora -> q1 <> empty_quorum ∧ q2 <> empty_quorum.
Proof.
    intros. apply quora_assumption_existence in H. inversion H.
    apply set_inter_elim in H0. inversion H0. split.
    { apply empty_spec_mem. exists x. apply set_mem_correct2. apply H1. }
    { apply empty_spec_mem. exists x. apply set_mem_correct2. apply H2. }
Qed.

Theorem quorum_nonempty_b : ∀ (q1 q2 : quorum),
    q1 ∈ quora -> q2 ∈ quora -> q1 <> empty_quorum ∧ q2 <> empty_quorum .
Proof.
    intros. specialize (quora_double q1 q2).
    intros H1. apply H1 in H.
    { apply quorum_nonempty_a. apply H. }
    { apply H0. }
Qed.

Theorem quorum_nonempty : ∀ (q : quorum),
    q ∈ quora -> q <> empty_quorum.
Proof.
    intros. specialize (quorum_nonempty_b q q).
    intros. apply H0 in H.
    { inversion H. apply H1. }
    { apply H. }
Qed.

Definition subset (x y : quorum) := ∀ (n : node), n ∈ x -> n ∈ y.

(********* Ballots *********)
Record ballot : Type := mkballot {
    balVal : value;
    balQrm: quorum;
    balVotes : quorum;
    balNum : number;
}.

Axiom Aeq_dec_ballot : ∀ (x y : ballot), {(balNum x) = (balNum y)} + {blt_number (balNum x) (balNum y) = true}.

(* Messages *)
Record message : Type := mkmsg {
    msgType : nat;
    msgNum : number;
    msgMaxVBal : number;
    msgMaxVal : value;
    msgAcc : node;
}.

(********* Paxos semantics *********)
Parameter accepted_ballots : set ballot.
Parameter acceptors : quorum.
Parameter values : set value.
Parameter numbers : list number.

Parameter maxBal : node -> number.
Parameter maxVBal : node -> number.
Parameter maxVal : node -> value.
Parameter messages : set message.

(* None value avoids implementing partial sets *)
Parameter None : value.
Definition None_excl : Prop := ~(None ∈ values).

Axiom ballot_uniq : ∀ (b1 b2 : ballot),
    b1 ∈ accepted_ballots -> b2 ∈ accepted_ballots ->
    b1 = b2 <-> (balNum b1) = (balNum b2).

Axiom ballot_ident : ∀ (b1 b2 : ballot),
    b1 ∈ accepted_ballots -> b2 ∈ accepted_ballots ->
    (balVal b1) = (balVal b2) ∧ (balQrm b1) = (balQrm b2) ∧ (balVotes b1) = (balVotes b2) ∧ (balNum b1) = (balNum b2)
    <-> b1 = b2.

Inductive voted_for_in : node -> value -> number -> Prop :=
    | cons_voted_for_in : ∀ (a : node) (v : value) (n : number),
        a ∈ acceptors -> v ∈ values -> n ∈ numbers ->
        (∃ (m : message), m ∈ messages ∧ (msgType m) = 4 ∧ (msgNum m) = n ∧ (msgMaxVal m) = v ∧ (msgAcc m) = a)
        -> voted_for_in a v n.

Inductive abstain : node -> number -> Prop :=
    | cons_abstrain : ∀ (a : node) (n : number),
        a ∈ acceptors -> n ∈ numbers ->
        (∀ (v : value), v ∈ values -> ~(voted_for_in a v n)) ∧
        blt_number n (maxBal a) = true
        -> abstain a n.

Inductive chosen_in : value -> number -> Prop :=
    | cons_chosen_in : ∀ (v : value) (n : number),
        v ∈ values -> n ∈ numbers ->
        (∃ (q : quorum), q ∈ quora -> (∀ (a : node), a ∈ q -> voted_for_in a v n))
        -> chosen_in v n.

Inductive chosen : value -> Prop :=
    | cons_chosen : ∀ (v : value),
        v ∈ values ->
        (∃ (n : number), n ∈ numbers -> chosen_in v n)
        -> chosen v.

(* Successful ballot registration semantics *)
Inductive register_quorum : ballot -> Prop :=
    | cons_register_quorum : ∀ (b : ballot),
        b ∈ accepted_ballots -> (balQrm b) ∈ quora -> register_quorum b.

Inductive register_value : ballot -> Prop :=
    | cons_register_value : ∀ (b : ballot),
        b ∈ accepted_ballots -> (balVal b) ∈ values -> register_value b.

Inductive register_number : ballot -> Prop :=
    | cons_register_number : ∀ (b : ballot),
        b ∈ accepted_ballots -> (balNum b) ∈ numbers -> register_number b.

Inductive register_quorum_votes : ballot -> Prop :=
    | cons_register_quorum_votes : ∀ (b : ballot),
        b ∈ accepted_ballots -> subset (balVotes b) (balQrm b) -> register_quorum_votes b.

Inductive register_vote_messages : ballot -> Prop :=
    | cons_register_vote_messages : ∀ (b : ballot) (a : node),
        b ∈ accepted_ballots -> a ∈ (balVotes b) ->
        (∃ (m : message), m ∈ messages 
            ∧ (msgType m) = 4
            ∧ (msgNum m) = (balNum b)
            ∧ (msgMaxVal m) = (balVal b)
            ∧ (msgAcc m) = a)
        -> register_vote_messages b.

Inductive register_votes : ballot -> Prop :=
    | cons_register_votes : ∀ (b : ballot),
        b ∈ accepted_ballots ->
        (∀ (a : node), a ∈ (balVotes b) -> voted_for_in a (balVal b) (balNum b))
        -> register_votes b.

Inductive register_quorum_acceptors : ballot -> Prop :=
    | cons_register_quorum_acceptors : ∀ (b : ballot),
        b ∈ accepted_ballots ->
        (∀ (a : node), a ∈ (balQrm b) -> a ∈ acceptors)
        -> register_quorum_acceptors b.

Inductive register_ballot : ballot -> Prop :=
    | cons_register_ballot : ∀ (b : ballot),
        register_quorum b ∧
        register_value b ∧
        register_number b ∧
        register_quorum_votes b ∧
        register_vote_messages b ∧
        register_votes b ∧
        register_quorum_acceptors b
        -> register_ballot b.

(* Definition of successful quorum in Paxos *)
Axiom quorum_voters_eq : ∀ (b : ballot),
    register_quorum_votes b ->
    subset (balQrm b) (balVotes b) ->
    (balQrm b) = (balVotes b).

(* Value is consistent with prior registered ballots *)
Inductive safe : value -> number -> Prop :=
    | cons_safe : ∀ (v : value) (n : number),
        v ∈ values -> n ∈ numbers ->
        (∀ (nx : number), nx ∈ numbers -> blt_number nx n = true ->
            (∃ (q : quorum),
                (∀ (b : ballot),
                    register_ballot b -> b ∈ accepted_ballots -> (nx = (balNum b)) ->
                    q = (balQrm b) ∧ (∀ (a : node), a ∈ q -> voted_for_in a v nx ∨ abstain a nx)
                )
            )
        )
        -> safe v n.

Inductive message_type_1 : message -> Prop :=
    | cons_message_type_1 : ∀ (m : message),
        m ∈ messages ->
        ((msgType m) = 1)
        -> message_type_1 m.

Inductive message_type_2 : message -> Prop :=
    | cons_message_type_2 : ∀ (m : message),
        m ∈ messages ->
        ((msgType m) = 2 -> leq_number (msgNum m) (maxBal (msgAcc m))
            ∧ ((msgMaxVal m) ∈ values
                ∧ (msgMaxVBal m) ∈ numbers
                ∧ voted_for_in (msgAcc m) (msgMaxVal m) ( msgMaxVBal m)
                ∨ ((msgMaxVal m) = None
                    ∧ (msgMaxVBal m) = numberID 0) ))
        -> message_type_2 m.

Inductive message_type_3 : message -> Prop :=
    | cons_message_type_3 : ∀ (m : message),
        m ∈ messages ->
        ((msgType m) = 3 -> (safe (msgMaxVal m) (msgNum m) ∧
            (∀ (mx : message), mx ∈ messages -> (msgType mx) = 3 ->
                (msgNum mx) = (msgNum m) -> mx = m)))
        -> message_type_3 m.

Inductive message_type_4 : message -> Prop :=
    | cons_message_type_4 : ∀ (m : message),
        m ∈ messages ->
        ((msgType m) = 4 -> (leq_number (msgNum m) (maxVBal (msgAcc m))
                                ∧ ∃ (mx : message), mx ∈ messages ∧
                                                    (msgType mx) = 3 ∧
                                                    (msgNum mx) = (msgNum m) ∧
                                                    (msgMaxVal mx) = (msgMaxVal m)))
        -> message_type_4 m.

Inductive message_invariant : Prop :=
    | cons_message_invariant : ∀ (m : message),
        m ∈ messages ->
        message_type_1 m ∧
        message_type_2 m ∧
        message_type_3 m ∧
        message_type_4 m
        -> message_invariant.

(********* Paxos results *********)

(*** Quorum on chosen value, a descendent of one-shot leader election ***)
Theorem quorum_vote_succeeds : ∀ (b : ballot) (a : node),
    register_ballot b -> b ∈ accepted_ballots ->
    a ∈ (balQrm b) -> (balQrm b) = (balVotes b) -> chosen (balVal b).
Proof.
    intros. apply cons_chosen.
    { inversion H; inversion H3; inversion H6; inversion H7. apply H10. }
    { inversion H; inversion H3; inversion H6; inversion H8; inversion H10; inversion H12; inversion H14; inversion H15.
        generalize (H18 a). intros. rewrite H2 in H1. apply H20 in H1.
        inversion H1. exists n. intros. apply (cons_chosen_in (balVal b) n).
        { assumption. }
        { assumption. }
        { exists (balQrm b). intros; generalize (H18 a1); intros.
            rewrite H2 in H30; apply H31 in H30; rewrite H27. apply H30. } }
Qed.

(* Quorum acceptors voted for that issue in that number *)
Theorem acceptors_voted_for_success : ∀ (a : node) (b : ballot),
    register_ballot b -> subset (balQrm b) (balVotes b) -> a ∈ (balQrm b) -> voted_for_in a (balVal b) (balNum b).
Proof.
    intros. inversion H. inversion H2.
    inversion H5. inversion H7. inversion H9. inversion H11. inversion H13.
    inversion H14. generalize (H17 a); intros.
    generalize (quorum_voters_eq b); intros.
    apply H20 in H10. 
        { rewrite H10 in H1. apply H19 in H1. apply H1. }
        { assumption. }
Qed.

Theorem voted_inv_for_safe : ∀ (a : node) (v : value) (n : number),
    message_invariant -> a ∈ acceptors ∧ v ∈ values ∧ n ∈ numbers ->
    voted_for_in a v n -> safe v n.
Proof.
    intros. inversion H. destruct H3; destruct H4; destruct H5. inversion H5.
Admitted.

(* Quorum is unconflicting at any register *)
Theorem safe_at_register : ∀ (b : ballot) (a : node),
    message_invariant -> register_ballot b -> a ∈ (balQrm b) -> subset (balQrm b) (balVotes b)
    -> safe (balVal b) (balNum b).
Proof.
    intros. inversion H. inversion H0. inversion H5. inversion H8. inversion H10. inversion H12. inversion H14. inversion H16.
    inversion H17. inversion H18. generalize (H23 a); intros. generalize (H20 a); intros.
    apply (voted_inv_for_safe a).
        { apply H. }
        { split.
         { apply H23 in H1. apply H1. }
         { split. 
            { inversion H9. apply H28. }
            { inversion H11. apply H28. } } }
        { apply quorum_voters_eq in H2.
            { rewrite H2 in H1. apply H26 in H1. apply H1. }
            { apply H13. } }
Qed.

(* Quorum voted consistently at subsequent register *)
Theorem safe_at_consistent_register : ∀ (b1 b2 : ballot),
    blt_number (balNum b1) (balNum b2) = true ->
    register_ballot b1 -> register_ballot b2 ->
    safe (balVal b2) (balNum b2) ->
    (∃ (a : node), a ∈ (balQrm b1) ∧ a ∈ (balQrm b2) ∧
        (voted_for_in a (balVal b2) (balNum b1) ∨ abstain a (balNum b1))).
Proof.
    intros. generalize (quora_assumption_existence (balQrm b1) (balQrm b2)); intros.
    inversion H0. inversion H4. inversion H6. inversion H0. inversion H11. inversion H13.
    generalize (quora_double (balQrm b1) (balQrm b2)); intros.
    apply H18 in H16. 
        { apply H3 in H16. inversion H16. exists x.
         inversion H2. split.
         { apply set_inter_elim1 in H19. apply H19. }
         { split.
            { apply set_inter_elim2 in H19. apply H19. }
            { generalize (H22 (balNum b1)); intros.
                inversion H14. inversion H27. inversion H28.
                apply H25 in H31.
                { inversion H31. generalize (H33 b1); intros.
                    apply H34 in H0. inversion H0. generalize (H36 x); intros.
                    { apply set_inter_elim1 in H19. symmetry in H35. rewrite H35 in H19.
                        apply H37 in H19. apply H19. }
                    { assumption. }
                    { reflexivity. } }
                { apply H. } } } }
        { destruct H1. destruct H1. destruct H1. apply H20. }
Qed.

Theorem single_voting : ∀ (a1 a2 : node) (n : number) (v1 v2 : value),
    message_invariant -> a1 ∈ acceptors -> a2 ∈ acceptors -> n ∈ numbers -> v1 ∈ values -> v2 ∈ values ->
    voted_for_in a1 v1 n ∧ voted_for_in a2 v2 n -> v1 = v2.
Proof.
Admitted.

(* Shared quorum necessitate value alignment  *)
Theorem voted_consistently_or_abstained : ∀ (b1 b2 : ballot) (a : node),
    message_invariant -> register_ballot b1 -> register_ballot b2 ->
    a ∈ (balQrm b1) -> a ∈ (balQrm b2) ->
    (voted_for_in a (balVal b2) (balNum b1) ∨ abstain a (balNum b1)) ->
    voted_for_in a (balVal b1) (balNum b1) -> (balVal b1) = (balVal b2).
Proof.
    intros. destruct H4.
    { apply (single_voting a a (balNum b1) (balVal b1) (balVal b2)).
        { apply H. }
        { destruct H0. destruct H0. destruct H6. destruct H7. destruct H8. destruct H9. destruct H10. destruct H11. generalize (H12 a); intros.
            apply H13 in H2. apply H2. }
        { destruct H0. destruct H0. destruct H6. destruct H7. destruct H8. destruct H9. destruct H10. destruct H11. generalize (H12 a); intros.
            apply H13 in H2. apply H2. }
        { destruct H0. destruct H0. destruct H6. destruct H7. destruct H7. apply H9. }
        { destruct H0. destruct H0. destruct H6. destruct H6. apply H8. }
        { destruct H1. destruct H1. destruct H6. destruct H6. apply H8. }
        { split.
            { apply H5. }
            { apply H4. } } }
    { inversion H4. inversion H8. generalize (H11 (balVal b1)); intros.
        destruct H0. destruct H0. destruct H14. destruct H14. apply H13 in H16. unfold not in H16. apply H16 in H5. contradiction. }
Qed.

(* Values are consistent with prior ballot numbers *)
Theorem prior_num_consistent : ∀ (b1 b2 : ballot),
    message_invariant -> register_ballot b1 -> register_ballot b2 ->
    subset (balQrm b1) (balVotes b1) -> subset (balQrm b2) (balVotes b2) ->
    blt_number (balNum b1) (balNum b2) = true ->
    (balVal b1) = (balVal b2).
Proof.
    intros. generalize (safe_at_consistent_register b1 b2); intros.
    apply H5 in H4. all: try assumption.
        { inversion H4. apply (voted_consistently_or_abstained b1 b2 x).
            all: inversion H6; inversion H8; try assumption.
            { generalize (acceptors_voted_for_success x b1); intros.
                { apply H11 in H0. all: try assumption. } } }
        { inversion H1. inversion H6. inversion H9. inversion H11. inversion H13. inversion H15. inversion H16.
            generalize (safe_at_register b2 a); intros. apply H22 in H1.
                { apply H1. }
                { apply H. }
                { apply quorum_voters_eq in H14.
                    { symmetry in H14. rewrite H14 in H19. apply H19. }
                    { apply H3. } }
                { apply H3. } }
Qed.

(* Values are consistent in identical registered ballots *)
Theorem eq_num_consistent : ∀ (b1 b2 : ballot),
    register_ballot b1 -> register_ballot b2 ->
    (balNum b1) = (balNum b2) ->
    (balVal b1) = (balVal b2).
Proof.
    intros. apply (ballot_ident b1 b2).
    { inversion H. inversion H2. inversion H4. apply H6. }
    { inversion H0. inversion H2. inversion H4. apply H6. }
    { apply (ballot_uniq b1 b2).
        { inversion H. inversion H2. inversion H4. apply H6. }
        { inversion H0. inversion H2. inversion H4. apply H6. }
        { apply H1. } }
Qed.

(*** Paxos consistency: any two passed ballots hold the same value ***)
Theorem consistent : ∀ (b1 b2 : ballot),
    message_invariant -> register_ballot b1 -> register_ballot b2 ->
    subset (balQrm b1) (balVotes b1) -> subset (balQrm b2) (balVotes b2) ->
    (balVal b1) = (balVal b2).
Proof.
    intros. destruct (Aeq_dec_ballot b1 b2).
    { apply (eq_num_consistent b1 b2). all: assumption. }
    { apply (prior_num_consistent b1 b2). all: assumption.  }
Qed.

End Paxos.