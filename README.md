# Paxos (Consistency), Proven.

Distributed consensus protocols allow distributed systems to agree on values among themselves without needing their members strictly online.

Paxos is a perrennial frontrunner in the marketplace of distributed consensus protocols. From its cryptic introduction – which earned its place in the back of publications' filing cabinets – to its somewhat ubiquity, Paxos has a storied history of misconception and modifications. Nonetheless, Leslie Lamport's original Paxos proposal [1] defies its complicated reputation – in fact, it is among the most obvious and straightforward protocols to answer the question.

Two obvious hopes of a consensus protocol are consistency – that there will not be more than one decided value – and progress – reliably deciding *some* value at all. Though Fischer, Lynch, and Paterson showed that progress cannot be guarunteed in a protocol like Paxos [2], consistency is provable on a model of Paxos.

So, let us explore how to construct such a model in Coq, from which these basic qualities may be proven.

## Priests or Nodes or Voters?

Leslie Lamport's original Paxos paper [1] described the protocol as an archaeological curiosity about the archaic parliamentary organization of a Greek isle *Paxos*, where parliamentary members were called *priests* who voted on *decrees*. Others have adapted this terminology to fit their analogy, implementation, or use case better over time. In this implementation, we do the same.

```coq
Inductive node : Type :=
    | nodeID : nat → node.

Inductive value : Type :=
    | valueID : nat → value.

Inductive number : Type :=
    | numberID : nat → number.

Axiom Aeq_dec : ∀ (n1 n2 : node), {n1 = n2} + {n1 <> n2}.
```

The voting elements are named *nodes*, who vote on *values*, in rounds called *numbers*.

When nodes vote, they hope to accumulate a quorum on a value. The collection of each quorum in the system is called the system's quora.

```coq
Definition quorum : Type := set node.
Definition empty_quorum : quorum := empty_set node.
Parameter quora : set (quorum).
```

It is an axiom of Paxos that two quora have at least one node in common.

```coq
Axiom quora_assumption_existence : ∀ (q1 q2 : quorum),
    q1 ∈ quora ∧ q2 ∈ quora → ∃ (n : node), n ∈ (set_inter Aeq_dec q1 q2).
```

This axiom allows an important fact: that any quorum admitted to the system quora is not empty.

```coq
Theorem quorum_nonempty_a : ∀ (q1 q2 : quorum),
    q1 ∈ quora ∧ q2 ∈ quora → q1 <> empty_quorum ∧ q2 <> empty_quorum.
Proof.
    intros. apply quora_assumption_existence in H. inversion H.
    apply set_inter_elim in H0. inversion H0. split.
    { apply empty_spec_mem. exists x. apply set_mem_correct2. apply H1. }
    { apply empty_spec_mem. exists x. apply set_mem_correct2. apply H2. }
Qed.

Theorem quorum_nonempty_b : ∀ (q1 q2 : quorum),
    q1 ∈ quora → q2 ∈ quora → q1 <> empty_quorum ∧ q2 <> empty_quorum .
Proof.
    intros. specialize (quora_double q1 q2).
    intros H1. apply H1 in H.
    { apply quorum_nonempty_a. apply H. }
    { apply H0. }
Qed.

Theorem quorum_nonempty : ∀ (q : quorum),
    q ∈ quora → q <> empty_quorum.
Proof.
    intros. specialize (quorum_nonempty_b q q).
    intros. apply H0 in H.
    { inversion H. apply H1. }
    { apply H. }
Qed.
```

## Ballots and Messages

Now that we have a notion of stakeholders, values, rounds, and outcomes of votes, we need a structure to mediate them. Enter ballots.

```coq
Record ballot : Type := mkballot {
    balVal : value; (* Value that a ballot is voting on *)
    balQrm: quorum; (* The tentative quorum supporting the ballot *)
    balVotes : quorum; (* The specialized votes on a ballot *)
    balNum : number; (* The number in voting *)
}.

Axiom Aeq_dec_ballot : ∀ (x y : ballot), {(balNum x) = (balNum y)} + {blt_number (balNum x) (balNum y) = true}.
```

Upon initiating a vote, voting, or recongizing a successful value, each node sends a message on the system.

```coq
Record message : Type := mkmsg {
    msgType : nat;
    msgNum : number;
    msgMaxVBal : number;
    msgMaxVal : value;
    msgAcc : node;
}.
```

The whole system may be modeled on these structures.

```coq
Parameter accepted_ballots : set ballot. (* Ballots with the support of acceptors *)
Parameter acceptors : quorum. (* Nodes agreeing on the value *)
Parameter values : set value. (* Values in accepted_ballots *)
Parameter numbers : list number. (* Numbers in accepted_ballots *)

Parameter maxBal : node -> number.
Parameter maxVBal : node -> number.
Parameter maxVal : node -> value.
Parameter messages : set message.

(* None value avoids implementing partial sets *)
Parameter None : value.
Definition None_excl : Prop := ~(None ∈ values).

(* Only one ballot can be accepted within a number *)
Axiom ballot_uniq : ∀ (b1 b2 : ballot),
    b1 ∈ accepted_ballots -> b2 ∈ accepted_ballots ->
    b1 = b2 <-> (balNum b1) = (balNum b2).

(* Definition of ballot equivalence *)
Axiom ballot_ident : ∀ (b1 b2 : ballot),
    b1 ∈ accepted_ballots -> b2 ∈ accepted_ballots ->
    (balVal b1) = (balVal b2) ∧ (balQrm b1) = (balQrm b2) ∧ (balVotes b1) = (balVotes b2) ∧ (balNum b1) = (balNum b2)
    <-> b1 = b2.
```

## Operationalizing the Model

Through these ballots, nodes can vote for a value in a number.

```coq
Inductive voted_for_in : node -> value -> number -> Prop :=
    | cons_voted_for_in : ∀ (a : node) (v : value) (n : number),
        a ∈ acceptors -> v ∈ values -> n ∈ numbers ->
        (∃ (m : message), m ∈ messages ∧ (msgType m) = 4 ∧ (msgNum m) = n ∧ (msgMaxVal m) = v ∧ (msgAcc m) = a)
        -> voted_for_in a v n.
```

If a node doesn't vote for a value in a number, it may instead abstain from that number.

```coq
Inductive abstain : node -> number -> Prop :=
    | cons_abstrain : ∀ (a : node) (n : number),
        a ∈ acceptors -> n ∈ numbers ->
        (∀ (v : value), v ∈ values -> ~(voted_for_in a v n)) ∧
        blt_number n (maxBal a) = true
        -> abstain a n.
```

If a value has the support of a quorum in a number, that value is *chosen* to be an accepted value.

```coq
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
```

### Ballot Registration Semantics
When a successful ballot is registered in the model, a few conditions must be met.

```coq
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
```

So, when a ballot succeeds, its quorum must be equal to the votes issued for that ballot.

```coq
Axiom quorum_voters_eq : ∀ (b : ballot),
    register_quorum_votes b ->
    subset (balQrm b) (balVotes b) ->
    (balQrm b) = (balVotes b).
```

### The Safety Condition

Finally, we may articulate the most important aspect of this model to proving consistency: the safety condition. When true, the votership for an accepted value issued in a number `n` is consistent with the votership in prior numbers `nx`. That is, nodes in prior votes either voted for the same value or abstained in the vote.

```coq
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
```

### Messages

We also give four types of messages:
1. A prepare request
2. A vote
3. An undervalued vote
4. A success

```coq

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
```

## Proving Properties

With the infrastructure of this model, we may now show important properties of Paxos.

### Vote Success Under Quorum

When a quorum admits a ballot to the accepted ballots, the value of the ballot will be a *chosen value*.

```coq
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
```

Furthermore, the acceptors of that ballot voted for that value.

```coq
Theorem acceptors_voted_for_success : ∀ (a : node) (b : ballot),
    register_ballot b -> subset (balQrm b) (balVotes b) ->
    a ∈ (balQrm b) -> voted_for_in a (balVal b) (balNum b).
Proof.
    intros. inversion H. inversion H2.
    inversion H5. inversion H7. inversion H9. inversion H11. inversion H13.
    inversion H14. generalize (H17 a); intros.
    generalize (quorum_voters_eq b); intros.
    apply H20 in H10. 
        { rewrite H10 in H1. apply H19 in H1. apply H1. }
        { assumption. }
Qed.
```

### Building to Consistency

We can say that, at any point of registration, the quorum meets the safety condition.
```coq
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
```

And, accordingly, the quorum will vote consistently at any subsequent registration.
```coq
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
```

Intuitively, if two registered ballots share quora, their values must align, too.
```coq
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
```

### Consistency of Paxos

Thanks to the equality decidability of ballots, we know there are two conditions: ballots either share numbers or one ballot is prior to another. By proving consistency in each of these cases, we may show consistency in general.

First, we show consistency between a ballot and a prior ballot.

```coq
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
```

Second, we show the consistency between a ballot and an equal-numbered (ergo identical) ballot.
```coq
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
```

Finally, we may accept the consistency of Paxos in general: that any two passed ballots agree in value.
```coq
Theorem consistent : ∀ (b1 b2 : ballot),
    message_invariant -> register_ballot b1 -> register_ballot b2 ->
    subset (balQrm b1) (balVotes b1) -> subset (balQrm b2) (balVotes b2) ->
    (balVal b1) = (balVal b2).
Proof.
    intros. destruct (Aeq_dec_ballot b1 b2).
    { apply (eq_num_consistent b1 b2). all: assumption. }
    { apply (prior_num_consistent b1 b2). all: assumption.  }
Qed.
```

### References
[1] Leslie Lamport. 1998. The part-time parliament. ACM Trans. Comput. Syst. 16, 2 (May 1998), 133–169. https://doi.org/10.1145/279227.279229
[2] Michael J. Fischer, Nancy A. Lynch, and Michael S. Paterson. 1985. Impossibility of distributed consensus with one faulty process. J. ACM 32, 2 (April 1985), 374–382. https://doi.org/10.1145/3149.214121