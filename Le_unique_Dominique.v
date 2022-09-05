(* These proofs are written by Dominique Larchey-Wendling 
  https://gist.github.com/mukeshtiwari/66a24eff6ac598e691c341d3faafb5d2
*)

Require Import Arith.  (* for lt_irrefl *)

Section eq_nat_pirr.

  Definition eq_0_inv {a} (e : 0 = a) : 
    match a as x return 0 = x -> Prop with 
      | 0   => fun f => f = eq_refl
      | S _ => fun _ => False
    end e :=
    match e with 
      | eq_refl => eq_refl 
    end.

  Definition eq_S_inv {a b} (e : S a = b) :
    match b as x return S a = x -> Type with
      | 0   => fun _ => False
      | S b => fun e => { f | e = eq_S a b f }
    end e :=
    match e with 
      | eq_refl => exist _ eq_refl eq_refl 
    end.

  Definition eq_0_pirr (e : 0 = 0) : 
    e = eq_refl := eq_0_inv e.

  Definition eq_S_pirr {a b} (e : S a = S b) : 
    {f : a = b | e = eq_S a b f} := eq_S_inv e.

  Theorem eq_nat_pirr {a : nat} : 
    forall e : a = a, e = eq_refl.
  Proof.
    induction a as [ | a IHa ]; intros e.
    + apply eq_0_pirr.
    + destruct (eq_S_pirr e) as (f & ->).
      rewrite (IHa f).
      reflexivity.
  Qed.

End eq_nat_pirr. 

Section le_pirr.

  Fact le_eq_inv {a b} (l : a <= b) (e : b = a) : 
    le_n a = eq_rect _ (le a) l _ e.
  Proof. 
    revert l e; intros [].
    + now intros e; rewrite (eq_nat_pirr e).
    + intros <-; exfalso; revert l; apply lt_irrefl.
  Qed.

  Fact le_eq_pirr {a} (l : a <= a) : l = le_n a.
  Proof. 
    generalize (le_eq_inv l eq_refl);
    simpl; auto. 
  Qed.

  Fact le_S_inv {a b} (l : a <= b) :
     match b as b' return a <= b' -> Prop with
       | 0   => fun _ => True
       | S b => fun l => a = S b \/ exists l', l = le_S _ _ l' 
     end l.
  Proof.
    destruct l.
    + destruct a; auto.
    + right; eauto.
  Qed.

  Fact le_S_pirr {a b} (lS : a <= S b) : a <= b -> exists l, lS = le_S _ _ l.
  Proof.
    destruct (le_S_inv lS) as [ -> | (l' & Hl') ].
    + intros H; exfalso; revert H; apply lt_irrefl.
    + eauto.
  Qed.

  Theorem le_pirr a : forall b (l₁ l₂ : a <= b), l₁ = l₂.
  Proof.
    refine (fix loop b l₁ { struct l₁ } := 
      match l₁ with 
        | le_n _      => fun l₂ => _
        | le_S _ b l₁ => fun l₂ => _
      end).
    + rewrite <- (le_eq_pirr l₂); reflexivity.
    + destruct (le_S_pirr l₂ l₁) as (? & ->).
      f_equal; apply loop.
  Qed.

  Variables 
    (n : nat) 
    (P : forall {m}, n <= m -> n <= m -> Prop)
    (P_n : P (le_n n) (le_n n))
    (P_S : forall m (l₁ l₂ : n <= m), P l₁ l₂ -> 
      P (le_S _ _ l₁) (le_S _ _ l₂)).

  Theorem le_le_ind : forall m (l₁ l₂ : n <= m), P l₁ l₂.
  Proof.
    refine (fix loop m l₁ { struct l₁ } := 
      match l₁ with 
        | le_n _      => fun l₂ => _
        | le_S _ b l₁ => fun l₂ => _
      end).
    + rewrite le_eq_pirr; apply P_n.
    + destruct (le_S_pirr l₂ l₁) as (? & ->).
      apply P_S, loop.
  Qed.

End le_pirr.

