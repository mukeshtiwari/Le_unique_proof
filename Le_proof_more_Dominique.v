(* As you can see that Dominique is Coq wizard :) *)

Require Import Arith Utf8.  (* for lt_irrefl *)

Section eq_nat_pirr.

  Definition eq_0_inv {a} (e : 0 = a) :
    match a return _ = a → Prop with
      | 0   => λ f, eq_refl = f
      | S _ => λ _, False
    end e :=
    match e with
      | eq_refl => eq_refl
    end.

  Definition eq_S_inv {a b} (e : S a = b) :
    match b return _ = b → Prop with
      | 0   => λ _, False
      | S b => λ e, ∃f, eq_S a b f = e
    end e :=
    match e with 
      | eq_refl => ex_intro _ eq_refl eq_refl
    end.

  (** Instances give what we want but just FYI *)

  Definition eq_0_pirr (e : 0 = 0) : eq_refl = e := eq_0_inv e.
  
  Definition eq_S_pirr {a b} (e : S a = S b) : 
  ∃f : a = b, eq_S a b f = e := eq_S_inv e.

  Fixpoint eq_nat_pirr {a : nat} : ∀e : a = a, eq_refl = e :=
    match a with
      | 0   => eq_0_inv
      | S a => λ e, let (f,Hf) := eq_S_inv e
                    in match Hf with
                      | eq_refl =>
                      match eq_nat_pirr f with
                        | eq_refl => eq_refl
                      end
                    end
    end.

End eq_nat_pirr.

Local Definition lt_irrefl' {a b} : S a = b → b ≤ a → False :=
  λ e, match e with eq_refl => lt_irrefl _ end.

Section le_pirr.

  Arguments le_n {_}.
  Arguments le_S {_ _}.

  Definition le_eq_inv {a b} (l : a ≤ b) : ∀e : b = a, le_n = eq_rect _ (le a) l _ e :=
    match l with
      | le_n   => λ e, match eq_nat_pirr e  with eq_refl => eq_refl end
      | le_S l => λ e, match lt_irrefl' e l with end
    end.

  Definition le_eq_pirr {a} (l : a ≤ a) : le_n = l := le_eq_inv l eq_refl.

  Definition le_S_inv {a b} (l : a ≤ b) :
     match b return _ ≤ b -> Prop with
       | 0   => λ _, True
       | S b => λ l, S b = a ∨ ∃l', le_S l' = l
     end l :=
     match l with
       | le_n =>
       match a with 
         | 0   => I
         | S _ => or_introl eq_refl
       end
       | le_S l' => or_intror (ex_intro _ l' eq_refl)
     end.

  Definition le_S_pirr {a b} (lS : a ≤ S b) : a ≤ b → ∃l, le_S l = lS :=
    match le_S_inv lS with
      | or_introl e => λ l, match lt_irrefl' e l with end
      | or_intror E => λ _, E
    end.

  Section le_pirr.

    Variable (a : nat).

    Fixpoint le_pirr {b} (l₁ : a ≤ b) { struct l₁ } : ∀l₂, l₁ = l₂ :=
      match l₁ with
        | le_n    => λ l₂, le_eq_pirr l₂
        | le_S l₁ => λ l₂, let (l,Hl) := le_S_pirr l₂ l₁
                           in match Hl with
                             | eq_refl =>
                             match le_pirr l₁ l with
                               | eq_refl => eq_refl
                             end
                           end
      end.

  End le_pirr.

  Section le_le_indd.

    Variables (a : nat) 
              (P : ∀ {b}, a ≤ b → a ≤ b → Prop)
              (P_n : @P a le_n le_n)
              (P_S : ∀ {b} {l₁ l₂ : a ≤ b}, P l₁ l₂ → P (le_S l₁) (le_S l₂)).

    Fixpoint le_le_indd {b} (l₁ : a ≤ b) { struct l₁ } : ∀l₂, P l₁ l₂ :=
      match l₁ with
        | le_n => λ l₂,
        match le_eq_pirr l₂ with
          | eq_refl => P_n
        end
        | le_S l₁ => λ l₂,
        let (l,Hl) := le_S_pirr l₂ l₁
        in match Hl with
          | eq_refl => P_S (le_le_indd l₁ l)
        end
      end.

  End le_le_indd.

  Theorem le_pirr' a : forall b (l₁ l₂ : a ≤ b), l₁ = l₂.
  Proof. now apply le_le_indd; intros; subst. Qed.

End le_pirr.

