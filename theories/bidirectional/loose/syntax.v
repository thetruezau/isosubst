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

Definition subst (sigma: fin->term) (P: term) :=
  (B (subst_term (sigma>>U>>uhd) (U P))).

Definition esubst (sigma: fin->term) (E: elim) :=
  (Be (subst_elim (sigma>>U>>uhd) (Ue E))).

Definition up_subst (sigma: fin->term) (P: term) :=
  (B (subst_term (up_elim (sigma>>U>>uhd)) (U P))).

(* --- *)

Proposition BU_is_id :
  (forall P, B (U P) = P) /\ (forall E, Be (Ue E) = E).
Proof.  
  apply mut_term_ind ; intros ; simpl ;
    try rewrite H ;
    try rewrite H0 ; auto.
Qed.

Fact lam_subst P P' sigma
  (HP': P' = up_subst sigma P):
  subst sigma (lam P) = lam P'.
Proof. now rewrite HP'. Qed.

Fact app_subst E E' sigma
  (HE': E' = esubst sigma E):
  subst sigma (app E) = app E'.
Proof. now rewrite HE'. Qed.

Fact evar_subst x sigma:
  esubst sigma (evar x) = hd (sigma x).
Proof.
  simpl. asimpl. now rewrite (proj1 BU_is_id). 
Qed.

Fact hd_subst P P' sigma
  (HP': P' = subst sigma P):
  esubst sigma (hd P) = hd P'.
Proof. now rewrite HP'. Qed.

Fact eapp_subst E E' Q Q' sigma
  (HE': E' = esubst sigma E)
  (HQ': Q' = subst sigma Q):
  esubst sigma (eapp E Q) = eapp E' Q'.
Proof. now rewrite HE', HQ'. Qed.
