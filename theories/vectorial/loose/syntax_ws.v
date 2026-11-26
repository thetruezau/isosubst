From unified Require Export syntax_ws.

Abbreviation uterm := syntax_ws.term.
Abbreviation ulam := syntax_ws.lam.
Abbreviation ulist := syntax_ws.list.
Abbreviation unil := syntax_ws.nil.
Abbreviation ucons := syntax_ws.cons.

Inductive term (n: nat): Type :=
| der (x: fin n) (l: list n)
| lam (t: term (S n)) 
| cut (t: term n) (l: list n) 

with list (n: nat): Type :=
| nil
| cons (u: term n) (l: list n).

Scheme sim_term_ind := Induction for term Sort Prop
  with sim_list_ind := Induction for list Sort Prop.

Combined Scheme mut_term_ind from sim_term_ind, sim_list_ind.

Arguments der {n}.
Arguments lam {n}.
Arguments cut {n}.

Arguments nil {n}.
Arguments cons {n}.

(** Append two lists *) 

Fixpoint append {n} (l: list n) (l': list n) : list n :=
  match l with
  | nil => l'
  | cons u l => cons u (append l l')
  end.

Notation "l + l'" := (append l l').

(** Mapping to unified system to derive substitution boilerplate *)

Fixpoint U {n: nat} (t: term n) : uterm n := 
  match t return uterm n with
  | der x l => mapp (var_elim x) (Us l)
  | lam t => ulam (U t)
  | cut t l => mapp (hd (U t)) (Us l)
  end with
Us {n: nat} (l: list n) : ulist n :=
  match l with
  | nil => unil
  | cons u l => ucons (U u) (Us l)
  end.

Fixpoint V {n: nat} (t: uterm n) : term n := 
  match t with
  | ulam t => lam (V t)
  | mapp E l => Ve E (Vs l)
  end with
Vs {n: nat} (l: ulist n) : list n :=
  match l with
  | unil => nil
  | ucons u l => cons (V u) (Vs l)
  end with
Ve {n: nat} (E: elim n) (l: list n): term n :=
  match E with
  | var_elim x => der x l
  | hd t => cut (V t) l
  | eapp E u => Ve E (cons (V u) l)
  end.

Definition subst {m: nat} {n: nat} (sigma: fin m->term n) (t: term m) :=
  (V (subst_term (sigma>>U>>hd) (U t))).

Definition lsubst {m: nat} {n: nat} (sigma: fin m->term n) (l: list m) :=
  (Vs (subst_list (sigma>>U>>hd) (Us l))).

Definition usubst {n: nat} (u: term n) (t: term (S n)) :=
  (V (subst_term (scons (hd (U u)) ids) (U t))).

Definition up_subst {m: nat} {n: nat}
  (sigma: fin m->term n) (t: term (S m)):=
  (V (subst_term (up_elim (sigma>>U>>hd)) (U t))).

(* --- *)

Proposition VU_is_id : forall n,
    (forall (t: term n), V (U t) = t) /\ (forall (l: list n), Vs (Us l) = l).
Proof.
  apply mut_term_ind; intros ; simpl ;
    try rewrite H ;
    try rewrite H0 ; auto.
Qed.

Fact der_subst m n (x: fin m) l l' (sigma: fin m-> term n)
  (Hl': l' = lsubst sigma l):
  subst sigma (der x l) = cut (sigma x) l'.
Proof.
  simpl. asimpl. subst. now rewrite (proj1 (VU_is_id n)). 
Qed.

Fact lam_subst m n (t: term (S m)) (sigma: fin m->term n) :
  subst sigma (lam t) = lam (up_subst sigma t).
Proof. easy. Qed.

Fact cut_subst m n t t' l l' (sigma: fin m->term n)
  (Ht': t' = subst sigma t)
  (Hl': l' = lsubst sigma l):
  subst sigma (cut t l) = cut t' l'.
Proof. now subst. Qed.

Fact nil_subst m n (sigma: fin m->term n) :
  lsubst sigma nil = nil.
Proof. easy. Qed.

Fact cons_subst m n u u' l l' (sigma: fin m->term n)
  (Hu': u' = subst sigma u)
  (Hl': l' = lsubst sigma l):
  lsubst sigma (cons u l) = cons u' l'.
Proof. now subst. Qed.
