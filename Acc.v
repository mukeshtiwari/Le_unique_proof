(* Easier way to understand Acc. The inductive case is 
basically transitivity. It took some time for me to 
realise it. *)

Require Import Lia.

Lemma nat_lt : 
  forall n : nat, 
  Acc (fun (x y : nat) => x < y) n.
Proof.
  induction n.
  + apply Acc_intro.
    intros ? Hy.
    nia.
  + apply Acc_intro.
    intros y Hy.
    apply Acc_intro.
    intros z Hz.
    (* Notice the two Acc_intro *)
    inversion IHn as [H].
    apply H.
    nia.
Qed.

(* Same proof *)
Lemma N_acc : 
  forall n : nat, Acc lt n.
Proof.
  induction n.
  + constructor; 
    intros ? Hy.
    nia.
  + apply Acc_intro.
    intros y Hy.
    apply Acc_intro.
    intros z Hz.
    inversion IHn as (Ih).
    apply Ih.
    nia. 
Qed.
