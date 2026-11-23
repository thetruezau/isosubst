From unified Require Export syntax.

Abbreviation uterm := syntax.term.
Abbreviation ulam := syntax.lam.
Abbreviation ulist := syntax.list.
Abbreviation unil := syntax.nil.
Abbreviation ucons := syntax.cons.

Inductive term: Type :=
| der (x: fin) (l: list)
| lam (t: term) 
| cut (t: term) (l: list) 

with list : Type :=
| nil
| cons (u: term) (l: list).

Scheme sim_term_ind := Induction for term Sort Prop
  with sim_list_ind := Induction for list Sort Prop.

Combined Scheme mut_term_ind from sim_term_ind, sim_list_ind.

Fixpoint U (t: term) : uterm := 
  match t with
  | der x l => app (var_elim x) (Us l)
  | lam t => ulam (U t)
  | cut t l => app (hd (U t)) (Us l)
  end with
Us (l: list) : ulist :=
  match l with
  | nil => unil
  | cons u l => ucons (U u) (Us l)
  end.

Fixpoint V (t: uterm) : term := 
  match t with
  | ulam t => lam (V t)
  | app E l => Ve E (Vs l)
  end with
Vs (l: ulist) : list :=
  match l with
  | unil => nil
  | ucons u l => cons (V u) (Vs l)
  end with
Ve (E: elim) (l: list): term :=
  match E with
  | var_elim x => der x l
  | hd t => cut (V t) l
  | eapp E u => Ve E (cons (V u) l)
  end.

Definition subst (sigma: fin->term) (t: term) :=
  (V (subst_term (sigma>>U>>hd) (U t))).

Definition lsubst (sigma: fin->term) (l: list) :=
  (Vs (subst_list (sigma>>U>>hd) (Us l))).

Definition up_subst (sigma: fin->term) (t: term) :=
  (V (subst_term (up_elim (sigma>>U>>hd)) (U t))).

(* --- *)

Proposition VU_is_id :
  (forall t, V (U t) = t) /\ (forall l, Vs (Us l) = l).
Proof.  
  apply mut_term_ind ; intros ; simpl ;
    try rewrite H ;
    try rewrite H0 ; auto.
Qed.

Fact der_subst x l l' sigma (Hl': l' = lsubst sigma l):
  subst sigma (der x l) = cut (sigma x) l'.
Proof.
  simpl. asimpl. rewrite (proj1 VU_is_id). now rewrite Hl'.
Qed.

Fact lam_subst t sigma :
  subst sigma (lam t) = lam (up_subst sigma t).
Proof. easy. Qed.

Fact cut_subst t t' l l' sigma
  (Ht': t' = subst sigma t)
  (Hl': l' = lsubst sigma l):
  subst sigma (cut t l) = cut t' l'.
Proof. now rewrite Ht',Hl'. Qed.

Fact nil_subst sigma :
  lsubst sigma nil = nil.
Proof. easy. Qed.

Fact cons_subst u u' l l' sigma
  (Hu': u' = subst sigma u)
  (Hl': l' = lsubst sigma l):
  lsubst sigma (cons u l) = cons u' l'.
Proof. now rewrite Hu',Hl'. Qed.
