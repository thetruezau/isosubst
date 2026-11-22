From unified Require Export syntax.

Abbreviation uterm := syntax.term.
Abbreviation uelim := syntax.elim.
Abbreviation ulam := syntax.lam.
Abbreviation uhd := syntax.hd.
Abbreviation uapp := syntax.app.
Abbreviation ueapp := syntax.eapp.

Inductive term: Type :=
| lam (P: term) 
| app (E: elim)

with elim: Type :=
| evar (x: fin)
| hd (P: term)
| eapp (E: elim) (Q: term).

Scheme sim_term_ind := Induction for term Sort Prop
  with sim_elim_ind := Induction for elim Sort Prop.

Combined Scheme mut_term_ind from sim_term_ind, sim_elim_ind.

Fixpoint U (P: term) : uterm := 
  match P with
  | lam P => ulam (U P)
  | app E => uapp (Ue E) nil
  end with
Ue (E: elim) : uelim :=
  match E with
  | evar x => var_elim x
  | hd P => uhd (U P)
  | eapp E Q => ueapp (Ue E) (U Q)
  end.

Fixpoint B (t: uterm): term := 
  match t with
  | ulam t => lam (B t)
  | uapp E l => app (Bs (Be E) l)
  end with
Bs (E: elim) (l: list): elim :=
  match l with
  | nil => E
  | cons u l => Bs (eapp E (B u)) l
  end with
Be (E: uelim): elim :=
  match E with
  | var_elim x => evar x
  | uhd t => hd (B t)
  | ueapp E u => eapp (Be E) (B u)
  end.

Definition rename (xi: fin->fin) (t: term) :=
  B (ren_term xi (U t)).
            
Definition subst (sigma: fin->term) (P: term) :=
  (B (subst_term (sigma>>U>>uhd) (U P))).

Definition esubst (sigma: fin->term) (E: elim) :=
  (Be (subst_elim (sigma>>U>>uhd) (Ue E))).

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
