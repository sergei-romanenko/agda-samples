Definition state : Type := (nat * nat * nat)%type.

Inductive datarace : state -> Prop :=
  | t1: forall (out : nat),
      datarace (out, 0, 0)
  | t2: forall (out : nat),
      datarace (S out, 0, 0) -> datarace (out, S 0, 0)
  | t3: forall (out scs : nat),
      datarace (S out, 0, scs) -> datarace (out, 0, S scs)
  | t4: forall (out cs scs : nat),
      datarace (out, S cs, scs) -> datarace (S out, cs, scs)
  | t5: forall (out cs scs : nat),
      datarace (out, cs, S scs) -> datarace (S out, cs, scs)
.

Inductive unsafe : state -> Prop := 
  | u1: forall (out cs scs : nat),
      unsafe (out, S cs, S scs)
.

Inductive datarace' : state -> Prop :=
  | w1: forall (out scs : nat),
      datarace'(out, 0, scs)
  | w2: forall (out : nat),
      datarace'(out, S 0, 0)
.

Lemma inclusion (c : state): datarace c -> datarace' c.
Proof.
intros T.
induction T; subst; try(inversion IHT; subst); constructor.
Qed.

Lemma safety (c : state): datarace' c -> ~unsafe c.
Proof.
intros W U.
inversion U; subst; inversion W.
Qed.

Theorem valid (c : state): datarace c -> ~unsafe c.
Proof.
intros H.
(* exact (safety c (inclusion c H)). *)
apply safety. apply inclusion. exact H.
Qed.
