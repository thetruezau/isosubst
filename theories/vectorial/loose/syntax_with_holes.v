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
Ve (E: elim): list->term :=
  match E with
  | var_elim x => der x
  | hd t => cut (V t)
  | eapp E u => Ve E (cons (V u) nil)
  end.

Inductive hole: Type :=
| hder (x: fin)
| hcut (t: term)
| heapp (h: hole) (u: term).

Definition Uh (h: hole) : elim :=
  match h with
  | hder x => var_elim x
  | hcut t => hd (U t)
  end.

Definition fill (h: hole) (l: list) :=
  match h with
  | hder x => der x l
  | hcut t => cut t l
  end.

Definition rename (xi: fin->fin) (t: term) :=
  V (ren_term xi (U t)).
            
Definition hrename (xi: fin->fin) (h: hole) :=
  match h with
  | hder x => hder (xi x)
  | hcut t => hcut (rename xi t)
  end.  

Definition subst (sigma: fin->hole) (t: term) :=
  (V (subst_term (sigma>>Uh) (U t))).

Definition lsubst (sigma: fin->hole) (l: list) :=
  (Vs (subst_list (sigma>>Uh) (Us l))).
                                 
Definition up (sigma: fin->hole) :=
  (scons (hder (var_zero)) (sigma >> (hrename (shift)))).

(* --- *)

Proposition VU_is_id :
  (forall t, V (U t) = t) /\ (forall l, Vs (Us l) = l).
Proof.  
  apply mut_term_ind ; intros ; simpl ;
    try rewrite H ;
    try rewrite H0 ; auto.
Qed.

Proposition VeUh_is_fill h :
  (forall l, Ve (Uh h) l = fill h l).
Proof.  
  destruct h ; intros ; simpl.
  - reflexivity.
  - now rewrite (proj1 VU_is_id).
Qed.

Fact der_subst x l l' sigma (Hl': l' = lsubst sigma l):
  subst sigma (der x l) = fill (sigma x) l'.
Proof.
  simpl. asimpl. rewrite VeUh_is_fill. now rewrite Hl'.
Qed.

Fact lam_subst t sigma :
  subst sigma (lam t) = lam (subst (up sigma) t).
Proof.
  simpl. asimpl. unfold up, subst. asimpl. simpl.
Qed.

