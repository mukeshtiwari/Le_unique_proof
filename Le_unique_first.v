From Coq Require Import PeanoNat Lia.
Require Import Eqdep_dec Arith.

Fact uip_nat {n : nat} (e : n = n) : e = eq_refl.
Proof. apply UIP_dec, eq_nat_dec. Qed.


Lemma le_unique : forall (m n : nat)
  (p q : m <= n), p = q.
Proof.
  intros ?. 
  refine(fix Fn n p {struct p} :=
    match p as p' in (_ <= np)
      return n = np -> forall (q : m <= np), 
        p' = q  
    with 
    | le_n _ => fun Heq q => 
      match q as q' in (_ <= nq)
        return forall (pf : nq = m),
          le_n m = (eq_rect _ _ q' _ pf)
      with
      | le_n _ => fun pf => _ 
      | le_S _ nt Hnt => fun pf => _ 
      end  eq_refl
    | le_S _ nt Hnt => fun Heq q => 
      match q as q' in (_ <= S np)
        return 
          forall (pf : np = nt),
            le_S _ nt Hnt =  
            eq_rect np (fun w => m <= S w) q' nt pf  
      with 
      | le_n _ => _ 
      | le_S _ nw Hnw => fun pf => _ 
      end eq_refl
    end eq_refl).
  + rewrite (uip_nat pf).
    exact eq_refl.
  + abstract nia.
  + clear Fn.
    destruct m.
    ++ exact idProp.
    ++ abstract nia.
  + subst; simpl.
    f_equal.
    apply Fn.
Qed.




Lemma le_pair_indd :
  forall (n : nat)
  (P : forall m : nat, n <= m -> n <= m -> Prop),
  P n (le_n n) (le_n n) ->
  (forall (m : nat) (Ha Hb : n <= m), P m Ha Hb ->
    P (S m) (le_S n m Ha) (le_S n m Hb)) ->
  forall (mt : nat) (Hna Hnb : n <= mt), P mt Hna Hnb.
Proof.
  intros ? ? Pa Pb.
  refine(
    fix Fn mt Hna :=
    match Hna as Hna' in (_ <= mtp) 
      return 
        mt = mtp -> 
        forall Hnb, P mtp Hna' Hnb
    with 
    | le_n _ => fun Hna Hnb => 
      match Hnb as Hnb' in (_ <= nt) 
        return 
          forall (pf : nt = n),
          P n (le_n n) (eq_rect nt _ Hnb' n pf)
      with 
      | le_n _ =>  fun pf => _ 
      | le_S _ nt Hnt => fun pf => _  
      end eq_refl
    | le_S _ nt Hnt => fun Heq Hnb => 
      match Hnb as Hnb' in (_ <= S np)
        return 
          forall (pf : np = nt),
          P (S nt) (le_S n nt Hnt) 
            (eq_rect np (fun w => n <= S w) Hnb' nt pf)
      with
      | le_n _ => _ 
      | le_S _ nw Hnw => fun pf => _ 
      end eq_refl
    end eq_refl).
  + rewrite (uip_nat pf).
    exact Pa.
  + abstract nia.
  + clear Fn.
    destruct n. 
    ++ exact idProp.
    ++ abstract nia.  
  +
    destruct mt as [|nt'].
    ++ abstract nia.
    ++ inversion Heq as (Heqp);
       clear Heq.
       specialize (Fn nt').
       subst.
       apply Pb. 
       apply Fn.
Qed.


Lemma le_pair_indd_simp : 
  forall (m n : nat)
  (p q : m <= n), p = q.
Proof.
  intros until q.
  apply (le_pair_indd _ (fun mt H₁ H₂ => H₁ = H₂)).
  + reflexivity.
  + intros mt Ha Hb Hc.
    subst; reflexivity.
Qed.  




(* Notice the {struct Hna}*)
Lemma le_pair_induction:
  forall (n : nat)
  (P : forall m : nat, n <= m -> n <= m -> Prop),
  P n (le_n n) (le_n n) ->
  (forall (m : nat) (Ha Hb : n <= m), P m Ha Hb ->
    P (S m) (le_S n m Ha) (le_S n m Hb)) ->
  forall (mt : nat) (Hna Hnb : n <= mt), P mt Hna Hnb.
Proof.
  intros ? ? Pa Pb.
  refine(
    fix Fn mt Hna {struct Hna}:=
    match Hna as Hna' in (_ <= mtp) 
      return 
        mt = mtp -> 
        forall Hnb, P mtp Hna' Hnb
    with 
    | le_n _ => fun Hna Hnb => 
      match Hnb as Hnb' in (_ <= nt) 
        return 
          forall (pf : nt = n),
          P n (le_n n) (eq_rect nt _ Hnb' n pf)
      with 
      | le_n _ =>  fun pf => _ 
      | le_S _ nt Hnt => fun pf => _  
      end eq_refl
    | le_S _ nt Hnt => fun Heq Hnb => 
      match Hnb as Hnb' in (_ <= S np)
        return 
          forall (pf : np = nt),
          P (S nt) (le_S n nt Hnt) 
            (eq_rect np (fun w => n <= S w) Hnb' nt pf)
      with
      | le_n _ => _ 
      | le_S _ nw Hnw => fun pf => _ 
      end eq_refl
    end eq_refl).
  + rewrite (uip_nat pf).
    exact Pa.
  + abstract nia.
  + clear Fn.
    destruct n. 
    ++ exact idProp.
    ++ abstract nia.  
  + subst.
    apply Pb, Fn.
Qed.




Lemma le_pair_induction_simp : 
  forall (m n : nat)
  (p q : m <= n), p = q.
Proof.
  intros until q.
  apply (le_pair_induction _ (fun mt H₁ H₂ => H₁ = H₂)).
  + reflexivity.
  + intros mt Ha Hb Hc.
    subst; reflexivity.
Qed.


