From headers Require Export unscoped.



Section termelimlist.
Inductive term  : Type :=
  | lam : ( term   ) -> term 
  | app : ( elim   ) -> ( list   ) -> term 
 with elim  : Type :=
  | var_elim : ( fin ) -> elim 
  | hd : ( term   ) -> elim 
  | eapp : ( elim   ) -> ( term   ) -> elim 
 with list  : Type :=
  | nil : list 
  | cons : ( term   ) -> ( list   ) -> list .

Lemma congr_lam  { s0 : term   } { t0 : term   } (H1 : s0 = t0) : lam  s0 = lam  t0 .
Proof. congruence. Qed.

Lemma congr_app  { s0 : elim   } { s1 : list   } { t0 : elim   } { t1 : list   } (H1 : s0 = t0) (H2 : s1 = t1) : app  s0 s1 = app  t0 t1 .
Proof. congruence. Qed.

Lemma congr_hd  { s0 : term   } { t0 : term   } (H1 : s0 = t0) : hd  s0 = hd  t0 .
Proof. congruence. Qed.

Lemma congr_eapp  { s0 : elim   } { s1 : term   } { t0 : elim   } { t1 : term   } (H1 : s0 = t0) (H2 : s1 = t1) : eapp  s0 s1 = eapp  t0 t1 .
Proof. congruence. Qed.

Lemma congr_nil  : nil  = nil  .
Proof. congruence. Qed.

Lemma congr_cons  { s0 : term   } { s1 : list   } { t0 : term   } { t1 : list   } (H1 : s0 = t0) (H2 : s1 = t1) : cons  s0 s1 = cons  t0 t1 .
Proof. congruence. Qed.

Definition upRen_elim_elim   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_term   (xielim : ( fin ) -> fin) (s : term ) : term  :=
    match s return term  with
    | lam  s0 => lam  ((ren_term (upRen_elim_elim xielim)) s0)
    | app  s0 s1 => app  ((ren_elim xielim) s0) ((ren_list xielim) s1)
    end
 with ren_elim   (xielim : ( fin ) -> fin) (s : elim ) : elim  :=
    match s return elim  with
    | var_elim  s => (var_elim ) (xielim s)
    | hd  s0 => hd  ((ren_term xielim) s0)
    | eapp  s0 s1 => eapp  ((ren_elim xielim) s0) ((ren_term xielim) s1)
    end
 with ren_list   (xielim : ( fin ) -> fin) (s : list ) : list  :=
    match s return list  with
    | nil   => nil 
    | cons  s0 s1 => cons  ((ren_term xielim) s0) ((ren_list xielim) s1)
    end.

Definition up_elim_elim   (sigma : ( fin ) -> elim ) : ( fin ) -> elim  :=
  (scons) ((var_elim ) (var_zero)) ((funcomp) (ren_elim (shift)) sigma).

Fixpoint subst_term   (sigmaelim : ( fin ) -> elim ) (s : term ) : term  :=
    match s return term  with
    | lam  s0 => lam  ((subst_term (up_elim_elim sigmaelim)) s0)
    | app  s0 s1 => app  ((subst_elim sigmaelim) s0) ((subst_list sigmaelim) s1)
    end
 with subst_elim   (sigmaelim : ( fin ) -> elim ) (s : elim ) : elim  :=
    match s return elim  with
    | var_elim  s => sigmaelim s
    | hd  s0 => hd  ((subst_term sigmaelim) s0)
    | eapp  s0 s1 => eapp  ((subst_elim sigmaelim) s0) ((subst_term sigmaelim) s1)
    end
 with subst_list   (sigmaelim : ( fin ) -> elim ) (s : list ) : list  :=
    match s return list  with
    | nil   => nil 
    | cons  s0 s1 => cons  ((subst_term sigmaelim) s0) ((subst_list sigmaelim) s1)
    end.

Definition upId_elim_elim  (sigma : ( fin ) -> elim ) (Eq : forall x, sigma x = (var_elim ) x) : forall x, (up_elim_elim sigma) x = (var_elim ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_elim (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_term  (sigmaelim : ( fin ) -> elim ) (Eqelim : forall x, sigmaelim x = (var_elim ) x) (s : term ) : subst_term sigmaelim s = s :=
    match s return subst_term sigmaelim s = s with
    | lam  s0 => congr_lam ((idSubst_term (up_elim_elim sigmaelim) (upId_elim_elim (_) Eqelim)) s0)
    | app  s0 s1 => congr_app ((idSubst_elim sigmaelim Eqelim) s0) ((idSubst_list sigmaelim Eqelim) s1)
    end
 with idSubst_elim  (sigmaelim : ( fin ) -> elim ) (Eqelim : forall x, sigmaelim x = (var_elim ) x) (s : elim ) : subst_elim sigmaelim s = s :=
    match s return subst_elim sigmaelim s = s with
    | var_elim  s => Eqelim s
    | hd  s0 => congr_hd ((idSubst_term sigmaelim Eqelim) s0)
    | eapp  s0 s1 => congr_eapp ((idSubst_elim sigmaelim Eqelim) s0) ((idSubst_term sigmaelim Eqelim) s1)
    end
 with idSubst_list  (sigmaelim : ( fin ) -> elim ) (Eqelim : forall x, sigmaelim x = (var_elim ) x) (s : list ) : subst_list sigmaelim s = s :=
    match s return subst_list sigmaelim s = s with
    | nil   => congr_nil 
    | cons  s0 s1 => congr_cons ((idSubst_term sigmaelim Eqelim) s0) ((idSubst_list sigmaelim Eqelim) s1)
    end.

Definition upExtRen_elim_elim   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_elim_elim xi) x = (upRen_elim_elim zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_term   (xielim : ( fin ) -> fin) (zetaelim : ( fin ) -> fin) (Eqelim : forall x, xielim x = zetaelim x) (s : term ) : ren_term xielim s = ren_term zetaelim s :=
    match s return ren_term xielim s = ren_term zetaelim s with
    | lam  s0 => congr_lam ((extRen_term (upRen_elim_elim xielim) (upRen_elim_elim zetaelim) (upExtRen_elim_elim (_) (_) Eqelim)) s0)
    | app  s0 s1 => congr_app ((extRen_elim xielim zetaelim Eqelim) s0) ((extRen_list xielim zetaelim Eqelim) s1)
    end
 with extRen_elim   (xielim : ( fin ) -> fin) (zetaelim : ( fin ) -> fin) (Eqelim : forall x, xielim x = zetaelim x) (s : elim ) : ren_elim xielim s = ren_elim zetaelim s :=
    match s return ren_elim xielim s = ren_elim zetaelim s with
    | var_elim  s => (ap) (var_elim ) (Eqelim s)
    | hd  s0 => congr_hd ((extRen_term xielim zetaelim Eqelim) s0)
    | eapp  s0 s1 => congr_eapp ((extRen_elim xielim zetaelim Eqelim) s0) ((extRen_term xielim zetaelim Eqelim) s1)
    end
 with extRen_list   (xielim : ( fin ) -> fin) (zetaelim : ( fin ) -> fin) (Eqelim : forall x, xielim x = zetaelim x) (s : list ) : ren_list xielim s = ren_list zetaelim s :=
    match s return ren_list xielim s = ren_list zetaelim s with
    | nil   => congr_nil 
    | cons  s0 s1 => congr_cons ((extRen_term xielim zetaelim Eqelim) s0) ((extRen_list xielim zetaelim Eqelim) s1)
    end.

Definition upExt_elim_elim   (sigma : ( fin ) -> elim ) (tau : ( fin ) -> elim ) (Eq : forall x, sigma x = tau x) : forall x, (up_elim_elim sigma) x = (up_elim_elim tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_elim (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_term   (sigmaelim : ( fin ) -> elim ) (tauelim : ( fin ) -> elim ) (Eqelim : forall x, sigmaelim x = tauelim x) (s : term ) : subst_term sigmaelim s = subst_term tauelim s :=
    match s return subst_term sigmaelim s = subst_term tauelim s with
    | lam  s0 => congr_lam ((ext_term (up_elim_elim sigmaelim) (up_elim_elim tauelim) (upExt_elim_elim (_) (_) Eqelim)) s0)
    | app  s0 s1 => congr_app ((ext_elim sigmaelim tauelim Eqelim) s0) ((ext_list sigmaelim tauelim Eqelim) s1)
    end
 with ext_elim   (sigmaelim : ( fin ) -> elim ) (tauelim : ( fin ) -> elim ) (Eqelim : forall x, sigmaelim x = tauelim x) (s : elim ) : subst_elim sigmaelim s = subst_elim tauelim s :=
    match s return subst_elim sigmaelim s = subst_elim tauelim s with
    | var_elim  s => Eqelim s
    | hd  s0 => congr_hd ((ext_term sigmaelim tauelim Eqelim) s0)
    | eapp  s0 s1 => congr_eapp ((ext_elim sigmaelim tauelim Eqelim) s0) ((ext_term sigmaelim tauelim Eqelim) s1)
    end
 with ext_list   (sigmaelim : ( fin ) -> elim ) (tauelim : ( fin ) -> elim ) (Eqelim : forall x, sigmaelim x = tauelim x) (s : list ) : subst_list sigmaelim s = subst_list tauelim s :=
    match s return subst_list sigmaelim s = subst_list tauelim s with
    | nil   => congr_nil 
    | cons  s0 s1 => congr_cons ((ext_term sigmaelim tauelim Eqelim) s0) ((ext_list sigmaelim tauelim Eqelim) s1)
    end.

Definition up_ren_ren_elim_elim    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_elim_elim tau) (upRen_elim_elim xi)) x = (upRen_elim_elim theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_term    (xielim : ( fin ) -> fin) (zetaelim : ( fin ) -> fin) (rhoelim : ( fin ) -> fin) (Eqelim : forall x, ((funcomp) zetaelim xielim) x = rhoelim x) (s : term ) : ren_term zetaelim (ren_term xielim s) = ren_term rhoelim s :=
    match s return ren_term zetaelim (ren_term xielim s) = ren_term rhoelim s with
    | lam  s0 => congr_lam ((compRenRen_term (upRen_elim_elim xielim) (upRen_elim_elim zetaelim) (upRen_elim_elim rhoelim) (up_ren_ren (_) (_) (_) Eqelim)) s0)
    | app  s0 s1 => congr_app ((compRenRen_elim xielim zetaelim rhoelim Eqelim) s0) ((compRenRen_list xielim zetaelim rhoelim Eqelim) s1)
    end
 with compRenRen_elim    (xielim : ( fin ) -> fin) (zetaelim : ( fin ) -> fin) (rhoelim : ( fin ) -> fin) (Eqelim : forall x, ((funcomp) zetaelim xielim) x = rhoelim x) (s : elim ) : ren_elim zetaelim (ren_elim xielim s) = ren_elim rhoelim s :=
    match s return ren_elim zetaelim (ren_elim xielim s) = ren_elim rhoelim s with
    | var_elim  s => (ap) (var_elim ) (Eqelim s)
    | hd  s0 => congr_hd ((compRenRen_term xielim zetaelim rhoelim Eqelim) s0)
    | eapp  s0 s1 => congr_eapp ((compRenRen_elim xielim zetaelim rhoelim Eqelim) s0) ((compRenRen_term xielim zetaelim rhoelim Eqelim) s1)
    end
 with compRenRen_list    (xielim : ( fin ) -> fin) (zetaelim : ( fin ) -> fin) (rhoelim : ( fin ) -> fin) (Eqelim : forall x, ((funcomp) zetaelim xielim) x = rhoelim x) (s : list ) : ren_list zetaelim (ren_list xielim s) = ren_list rhoelim s :=
    match s return ren_list zetaelim (ren_list xielim s) = ren_list rhoelim s with
    | nil   => congr_nil 
    | cons  s0 s1 => congr_cons ((compRenRen_term xielim zetaelim rhoelim Eqelim) s0) ((compRenRen_list xielim zetaelim rhoelim Eqelim) s1)
    end.

Definition up_ren_subst_elim_elim    (xi : ( fin ) -> fin) (tau : ( fin ) -> elim ) (theta : ( fin ) -> elim ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_elim_elim tau) (upRen_elim_elim xi)) x = (up_elim_elim theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_elim (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_term    (xielim : ( fin ) -> fin) (tauelim : ( fin ) -> elim ) (thetaelim : ( fin ) -> elim ) (Eqelim : forall x, ((funcomp) tauelim xielim) x = thetaelim x) (s : term ) : subst_term tauelim (ren_term xielim s) = subst_term thetaelim s :=
    match s return subst_term tauelim (ren_term xielim s) = subst_term thetaelim s with
    | lam  s0 => congr_lam ((compRenSubst_term (upRen_elim_elim xielim) (up_elim_elim tauelim) (up_elim_elim thetaelim) (up_ren_subst_elim_elim (_) (_) (_) Eqelim)) s0)
    | app  s0 s1 => congr_app ((compRenSubst_elim xielim tauelim thetaelim Eqelim) s0) ((compRenSubst_list xielim tauelim thetaelim Eqelim) s1)
    end
 with compRenSubst_elim    (xielim : ( fin ) -> fin) (tauelim : ( fin ) -> elim ) (thetaelim : ( fin ) -> elim ) (Eqelim : forall x, ((funcomp) tauelim xielim) x = thetaelim x) (s : elim ) : subst_elim tauelim (ren_elim xielim s) = subst_elim thetaelim s :=
    match s return subst_elim tauelim (ren_elim xielim s) = subst_elim thetaelim s with
    | var_elim  s => Eqelim s
    | hd  s0 => congr_hd ((compRenSubst_term xielim tauelim thetaelim Eqelim) s0)
    | eapp  s0 s1 => congr_eapp ((compRenSubst_elim xielim tauelim thetaelim Eqelim) s0) ((compRenSubst_term xielim tauelim thetaelim Eqelim) s1)
    end
 with compRenSubst_list    (xielim : ( fin ) -> fin) (tauelim : ( fin ) -> elim ) (thetaelim : ( fin ) -> elim ) (Eqelim : forall x, ((funcomp) tauelim xielim) x = thetaelim x) (s : list ) : subst_list tauelim (ren_list xielim s) = subst_list thetaelim s :=
    match s return subst_list tauelim (ren_list xielim s) = subst_list thetaelim s with
    | nil   => congr_nil 
    | cons  s0 s1 => congr_cons ((compRenSubst_term xielim tauelim thetaelim Eqelim) s0) ((compRenSubst_list xielim tauelim thetaelim Eqelim) s1)
    end.

Definition up_subst_ren_elim_elim    (sigma : ( fin ) -> elim ) (zetaelim : ( fin ) -> fin) (theta : ( fin ) -> elim ) (Eq : forall x, ((funcomp) (ren_elim zetaelim) sigma) x = theta x) : forall x, ((funcomp) (ren_elim (upRen_elim_elim zetaelim)) (up_elim_elim sigma)) x = (up_elim_elim theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_elim (shift) (upRen_elim_elim zetaelim) ((funcomp) (shift) zetaelim) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_elim zetaelim (shift) ((funcomp) (shift) zetaelim) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_elim (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_term    (sigmaelim : ( fin ) -> elim ) (zetaelim : ( fin ) -> fin) (thetaelim : ( fin ) -> elim ) (Eqelim : forall x, ((funcomp) (ren_elim zetaelim) sigmaelim) x = thetaelim x) (s : term ) : ren_term zetaelim (subst_term sigmaelim s) = subst_term thetaelim s :=
    match s return ren_term zetaelim (subst_term sigmaelim s) = subst_term thetaelim s with
    | lam  s0 => congr_lam ((compSubstRen_term (up_elim_elim sigmaelim) (upRen_elim_elim zetaelim) (up_elim_elim thetaelim) (up_subst_ren_elim_elim (_) (_) (_) Eqelim)) s0)
    | app  s0 s1 => congr_app ((compSubstRen_elim sigmaelim zetaelim thetaelim Eqelim) s0) ((compSubstRen_list sigmaelim zetaelim thetaelim Eqelim) s1)
    end
 with compSubstRen_elim    (sigmaelim : ( fin ) -> elim ) (zetaelim : ( fin ) -> fin) (thetaelim : ( fin ) -> elim ) (Eqelim : forall x, ((funcomp) (ren_elim zetaelim) sigmaelim) x = thetaelim x) (s : elim ) : ren_elim zetaelim (subst_elim sigmaelim s) = subst_elim thetaelim s :=
    match s return ren_elim zetaelim (subst_elim sigmaelim s) = subst_elim thetaelim s with
    | var_elim  s => Eqelim s
    | hd  s0 => congr_hd ((compSubstRen_term sigmaelim zetaelim thetaelim Eqelim) s0)
    | eapp  s0 s1 => congr_eapp ((compSubstRen_elim sigmaelim zetaelim thetaelim Eqelim) s0) ((compSubstRen_term sigmaelim zetaelim thetaelim Eqelim) s1)
    end
 with compSubstRen_list    (sigmaelim : ( fin ) -> elim ) (zetaelim : ( fin ) -> fin) (thetaelim : ( fin ) -> elim ) (Eqelim : forall x, ((funcomp) (ren_elim zetaelim) sigmaelim) x = thetaelim x) (s : list ) : ren_list zetaelim (subst_list sigmaelim s) = subst_list thetaelim s :=
    match s return ren_list zetaelim (subst_list sigmaelim s) = subst_list thetaelim s with
    | nil   => congr_nil 
    | cons  s0 s1 => congr_cons ((compSubstRen_term sigmaelim zetaelim thetaelim Eqelim) s0) ((compSubstRen_list sigmaelim zetaelim thetaelim Eqelim) s1)
    end.

Definition up_subst_subst_elim_elim    (sigma : ( fin ) -> elim ) (tauelim : ( fin ) -> elim ) (theta : ( fin ) -> elim ) (Eq : forall x, ((funcomp) (subst_elim tauelim) sigma) x = theta x) : forall x, ((funcomp) (subst_elim (up_elim_elim tauelim)) (up_elim_elim sigma)) x = (up_elim_elim theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_elim (shift) (up_elim_elim tauelim) ((funcomp) (up_elim_elim tauelim) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_elim tauelim (shift) ((funcomp) (ren_elim (shift)) tauelim) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_elim (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_term    (sigmaelim : ( fin ) -> elim ) (tauelim : ( fin ) -> elim ) (thetaelim : ( fin ) -> elim ) (Eqelim : forall x, ((funcomp) (subst_elim tauelim) sigmaelim) x = thetaelim x) (s : term ) : subst_term tauelim (subst_term sigmaelim s) = subst_term thetaelim s :=
    match s return subst_term tauelim (subst_term sigmaelim s) = subst_term thetaelim s with
    | lam  s0 => congr_lam ((compSubstSubst_term (up_elim_elim sigmaelim) (up_elim_elim tauelim) (up_elim_elim thetaelim) (up_subst_subst_elim_elim (_) (_) (_) Eqelim)) s0)
    | app  s0 s1 => congr_app ((compSubstSubst_elim sigmaelim tauelim thetaelim Eqelim) s0) ((compSubstSubst_list sigmaelim tauelim thetaelim Eqelim) s1)
    end
 with compSubstSubst_elim    (sigmaelim : ( fin ) -> elim ) (tauelim : ( fin ) -> elim ) (thetaelim : ( fin ) -> elim ) (Eqelim : forall x, ((funcomp) (subst_elim tauelim) sigmaelim) x = thetaelim x) (s : elim ) : subst_elim tauelim (subst_elim sigmaelim s) = subst_elim thetaelim s :=
    match s return subst_elim tauelim (subst_elim sigmaelim s) = subst_elim thetaelim s with
    | var_elim  s => Eqelim s
    | hd  s0 => congr_hd ((compSubstSubst_term sigmaelim tauelim thetaelim Eqelim) s0)
    | eapp  s0 s1 => congr_eapp ((compSubstSubst_elim sigmaelim tauelim thetaelim Eqelim) s0) ((compSubstSubst_term sigmaelim tauelim thetaelim Eqelim) s1)
    end
 with compSubstSubst_list    (sigmaelim : ( fin ) -> elim ) (tauelim : ( fin ) -> elim ) (thetaelim : ( fin ) -> elim ) (Eqelim : forall x, ((funcomp) (subst_elim tauelim) sigmaelim) x = thetaelim x) (s : list ) : subst_list tauelim (subst_list sigmaelim s) = subst_list thetaelim s :=
    match s return subst_list tauelim (subst_list sigmaelim s) = subst_list thetaelim s with
    | nil   => congr_nil 
    | cons  s0 s1 => congr_cons ((compSubstSubst_term sigmaelim tauelim thetaelim Eqelim) s0) ((compSubstSubst_list sigmaelim tauelim thetaelim Eqelim) s1)
    end.

Definition rinstInst_up_elim_elim   (xi : ( fin ) -> fin) (sigma : ( fin ) -> elim ) (Eq : forall x, ((funcomp) (var_elim ) xi) x = sigma x) : forall x, ((funcomp) (var_elim ) (upRen_elim_elim xi)) x = (up_elim_elim sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_elim (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_term   (xielim : ( fin ) -> fin) (sigmaelim : ( fin ) -> elim ) (Eqelim : forall x, ((funcomp) (var_elim ) xielim) x = sigmaelim x) (s : term ) : ren_term xielim s = subst_term sigmaelim s :=
    match s return ren_term xielim s = subst_term sigmaelim s with
    | lam  s0 => congr_lam ((rinst_inst_term (upRen_elim_elim xielim) (up_elim_elim sigmaelim) (rinstInst_up_elim_elim (_) (_) Eqelim)) s0)
    | app  s0 s1 => congr_app ((rinst_inst_elim xielim sigmaelim Eqelim) s0) ((rinst_inst_list xielim sigmaelim Eqelim) s1)
    end
 with rinst_inst_elim   (xielim : ( fin ) -> fin) (sigmaelim : ( fin ) -> elim ) (Eqelim : forall x, ((funcomp) (var_elim ) xielim) x = sigmaelim x) (s : elim ) : ren_elim xielim s = subst_elim sigmaelim s :=
    match s return ren_elim xielim s = subst_elim sigmaelim s with
    | var_elim  s => Eqelim s
    | hd  s0 => congr_hd ((rinst_inst_term xielim sigmaelim Eqelim) s0)
    | eapp  s0 s1 => congr_eapp ((rinst_inst_elim xielim sigmaelim Eqelim) s0) ((rinst_inst_term xielim sigmaelim Eqelim) s1)
    end
 with rinst_inst_list   (xielim : ( fin ) -> fin) (sigmaelim : ( fin ) -> elim ) (Eqelim : forall x, ((funcomp) (var_elim ) xielim) x = sigmaelim x) (s : list ) : ren_list xielim s = subst_list sigmaelim s :=
    match s return ren_list xielim s = subst_list sigmaelim s with
    | nil   => congr_nil 
    | cons  s0 s1 => congr_cons ((rinst_inst_term xielim sigmaelim Eqelim) s0) ((rinst_inst_list xielim sigmaelim Eqelim) s1)
    end.

Lemma rinstInst_term   (xielim : ( fin ) -> fin) : ren_term xielim = subst_term ((funcomp) (var_elim ) xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_term xielim (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_elim   (xielim : ( fin ) -> fin) : ren_elim xielim = subst_elim ((funcomp) (var_elim ) xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_elim xielim (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_list   (xielim : ( fin ) -> fin) : ren_list xielim = subst_list ((funcomp) (var_elim ) xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_list xielim (_) (fun n => eq_refl) x)). Qed.

Lemma instId_term  : subst_term (var_elim ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_term (var_elim ) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_elim  : subst_elim (var_elim ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_elim (var_elim ) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_list  : subst_list (var_elim ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_list (var_elim ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_term  : @ren_term   (id) = id .
Proof. exact ((eq_trans) (rinstInst_term ((id) (_))) instId_term). Qed.

Lemma rinstId_elim  : @ren_elim   (id) = id .
Proof. exact ((eq_trans) (rinstInst_elim ((id) (_))) instId_elim). Qed.

Lemma rinstId_list  : @ren_list   (id) = id .
Proof. exact ((eq_trans) (rinstInst_list ((id) (_))) instId_list). Qed.

Lemma varL_elim   (sigmaelim : ( fin ) -> elim ) : (funcomp) (subst_elim sigmaelim) (var_elim ) = sigmaelim .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_elim   (xielim : ( fin ) -> fin) : (funcomp) (ren_elim xielim) (var_elim ) = (funcomp) (var_elim ) xielim .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_term    (sigmaelim : ( fin ) -> elim ) (tauelim : ( fin ) -> elim ) (s : term ) : subst_term tauelim (subst_term sigmaelim s) = subst_term ((funcomp) (subst_elim tauelim) sigmaelim) s .
Proof. exact (compSubstSubst_term sigmaelim tauelim (_) (fun n => eq_refl) s). Qed.

Lemma compComp_elim    (sigmaelim : ( fin ) -> elim ) (tauelim : ( fin ) -> elim ) (s : elim ) : subst_elim tauelim (subst_elim sigmaelim s) = subst_elim ((funcomp) (subst_elim tauelim) sigmaelim) s .
Proof. exact (compSubstSubst_elim sigmaelim tauelim (_) (fun n => eq_refl) s). Qed.

Lemma compComp_list    (sigmaelim : ( fin ) -> elim ) (tauelim : ( fin ) -> elim ) (s : list ) : subst_list tauelim (subst_list sigmaelim s) = subst_list ((funcomp) (subst_elim tauelim) sigmaelim) s .
Proof. exact (compSubstSubst_list sigmaelim tauelim (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_term    (sigmaelim : ( fin ) -> elim ) (tauelim : ( fin ) -> elim ) : (funcomp) (subst_term tauelim) (subst_term sigmaelim) = subst_term ((funcomp) (subst_elim tauelim) sigmaelim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_term sigmaelim tauelim n)). Qed.

Lemma compComp'_elim    (sigmaelim : ( fin ) -> elim ) (tauelim : ( fin ) -> elim ) : (funcomp) (subst_elim tauelim) (subst_elim sigmaelim) = subst_elim ((funcomp) (subst_elim tauelim) sigmaelim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_elim sigmaelim tauelim n)). Qed.

Lemma compComp'_list    (sigmaelim : ( fin ) -> elim ) (tauelim : ( fin ) -> elim ) : (funcomp) (subst_list tauelim) (subst_list sigmaelim) = subst_list ((funcomp) (subst_elim tauelim) sigmaelim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_list sigmaelim tauelim n)). Qed.

Lemma compRen_term    (sigmaelim : ( fin ) -> elim ) (zetaelim : ( fin ) -> fin) (s : term ) : ren_term zetaelim (subst_term sigmaelim s) = subst_term ((funcomp) (ren_elim zetaelim) sigmaelim) s .
Proof. exact (compSubstRen_term sigmaelim zetaelim (_) (fun n => eq_refl) s). Qed.

Lemma compRen_elim    (sigmaelim : ( fin ) -> elim ) (zetaelim : ( fin ) -> fin) (s : elim ) : ren_elim zetaelim (subst_elim sigmaelim s) = subst_elim ((funcomp) (ren_elim zetaelim) sigmaelim) s .
Proof. exact (compSubstRen_elim sigmaelim zetaelim (_) (fun n => eq_refl) s). Qed.

Lemma compRen_list    (sigmaelim : ( fin ) -> elim ) (zetaelim : ( fin ) -> fin) (s : list ) : ren_list zetaelim (subst_list sigmaelim s) = subst_list ((funcomp) (ren_elim zetaelim) sigmaelim) s .
Proof. exact (compSubstRen_list sigmaelim zetaelim (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_term    (sigmaelim : ( fin ) -> elim ) (zetaelim : ( fin ) -> fin) : (funcomp) (ren_term zetaelim) (subst_term sigmaelim) = subst_term ((funcomp) (ren_elim zetaelim) sigmaelim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_term sigmaelim zetaelim n)). Qed.

Lemma compRen'_elim    (sigmaelim : ( fin ) -> elim ) (zetaelim : ( fin ) -> fin) : (funcomp) (ren_elim zetaelim) (subst_elim sigmaelim) = subst_elim ((funcomp) (ren_elim zetaelim) sigmaelim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_elim sigmaelim zetaelim n)). Qed.

Lemma compRen'_list    (sigmaelim : ( fin ) -> elim ) (zetaelim : ( fin ) -> fin) : (funcomp) (ren_list zetaelim) (subst_list sigmaelim) = subst_list ((funcomp) (ren_elim zetaelim) sigmaelim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_list sigmaelim zetaelim n)). Qed.

Lemma renComp_term    (xielim : ( fin ) -> fin) (tauelim : ( fin ) -> elim ) (s : term ) : subst_term tauelim (ren_term xielim s) = subst_term ((funcomp) tauelim xielim) s .
Proof. exact (compRenSubst_term xielim tauelim (_) (fun n => eq_refl) s). Qed.

Lemma renComp_elim    (xielim : ( fin ) -> fin) (tauelim : ( fin ) -> elim ) (s : elim ) : subst_elim tauelim (ren_elim xielim s) = subst_elim ((funcomp) tauelim xielim) s .
Proof. exact (compRenSubst_elim xielim tauelim (_) (fun n => eq_refl) s). Qed.

Lemma renComp_list    (xielim : ( fin ) -> fin) (tauelim : ( fin ) -> elim ) (s : list ) : subst_list tauelim (ren_list xielim s) = subst_list ((funcomp) tauelim xielim) s .
Proof. exact (compRenSubst_list xielim tauelim (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_term    (xielim : ( fin ) -> fin) (tauelim : ( fin ) -> elim ) : (funcomp) (subst_term tauelim) (ren_term xielim) = subst_term ((funcomp) tauelim xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_term xielim tauelim n)). Qed.

Lemma renComp'_elim    (xielim : ( fin ) -> fin) (tauelim : ( fin ) -> elim ) : (funcomp) (subst_elim tauelim) (ren_elim xielim) = subst_elim ((funcomp) tauelim xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_elim xielim tauelim n)). Qed.

Lemma renComp'_list    (xielim : ( fin ) -> fin) (tauelim : ( fin ) -> elim ) : (funcomp) (subst_list tauelim) (ren_list xielim) = subst_list ((funcomp) tauelim xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_list xielim tauelim n)). Qed.

Lemma renRen_term    (xielim : ( fin ) -> fin) (zetaelim : ( fin ) -> fin) (s : term ) : ren_term zetaelim (ren_term xielim s) = ren_term ((funcomp) zetaelim xielim) s .
Proof. exact (compRenRen_term xielim zetaelim (_) (fun n => eq_refl) s). Qed.

Lemma renRen_elim    (xielim : ( fin ) -> fin) (zetaelim : ( fin ) -> fin) (s : elim ) : ren_elim zetaelim (ren_elim xielim s) = ren_elim ((funcomp) zetaelim xielim) s .
Proof. exact (compRenRen_elim xielim zetaelim (_) (fun n => eq_refl) s). Qed.

Lemma renRen_list    (xielim : ( fin ) -> fin) (zetaelim : ( fin ) -> fin) (s : list ) : ren_list zetaelim (ren_list xielim s) = ren_list ((funcomp) zetaelim xielim) s .
Proof. exact (compRenRen_list xielim zetaelim (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_term    (xielim : ( fin ) -> fin) (zetaelim : ( fin ) -> fin) : (funcomp) (ren_term zetaelim) (ren_term xielim) = ren_term ((funcomp) zetaelim xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_term xielim zetaelim n)). Qed.

Lemma renRen'_elim    (xielim : ( fin ) -> fin) (zetaelim : ( fin ) -> fin) : (funcomp) (ren_elim zetaelim) (ren_elim xielim) = ren_elim ((funcomp) zetaelim xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_elim xielim zetaelim n)). Qed.

Lemma renRen'_list    (xielim : ( fin ) -> fin) (zetaelim : ( fin ) -> fin) : (funcomp) (ren_list zetaelim) (ren_list xielim) = ren_list ((funcomp) zetaelim xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_list xielim zetaelim n)). Qed.

End termelimlist.















Global Instance Subst_term   : Subst1 (( fin ) -> elim ) (term ) (term ) := @subst_term   .

Global Instance Subst_elim   : Subst1 (( fin ) -> elim ) (elim ) (elim ) := @subst_elim   .

Global Instance Subst_list   : Subst1 (( fin ) -> elim ) (list ) (list ) := @subst_list   .

Global Instance Ren_term   : Ren1 (( fin ) -> fin) (term ) (term ) := @ren_term   .

Global Instance Ren_elim   : Ren1 (( fin ) -> fin) (elim ) (elim ) := @ren_elim   .

Global Instance Ren_list   : Ren1 (( fin ) -> fin) (list ) (list ) := @ren_list   .

Global Instance VarInstance_elim  : Var (fin) (elim ) := @var_elim  .

Notation "x '__elim'" := (var_elim x) (at level 5, format "x __elim") : subst_scope.

Notation "x '__elim'" := (@ids (_) (_) VarInstance_elim x) (at level 5, only printing, format "x __elim") : subst_scope.

Notation "'var'" := (var_elim) (only printing, at level 1) : subst_scope.

Class Up_elim X Y := up_elim : ( X ) -> Y.

Notation "↑__elim" := (up_elim) (only printing) : subst_scope.

Notation "↑__elim" := (up_elim_elim) (only printing) : subst_scope.

Global Instance Up_elim_elim   : Up_elim (_) (_) := @up_elim_elim   .

Notation "s [ sigmaelim ]" := (subst_term sigmaelim s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaelim ]" := (subst_term sigmaelim) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xielim ⟩" := (ren_term xielim s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xielim ⟩" := (ren_term xielim) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaelim ]" := (subst_elim sigmaelim s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaelim ]" := (subst_elim sigmaelim) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xielim ⟩" := (ren_elim xielim s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xielim ⟩" := (ren_elim xielim) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaelim ]" := (subst_list sigmaelim s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaelim ]" := (subst_list sigmaelim) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xielim ⟩" := (ren_list xielim s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xielim ⟩" := (ren_list xielim) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_term,  Subst_elim,  Subst_list,  Ren_term,  Ren_elim,  Ren_list,  VarInstance_elim.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_term,  Subst_elim,  Subst_list,  Ren_term,  Ren_elim,  Ren_list,  VarInstance_elim in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_term| progress rewrite ?compComp_term| progress rewrite ?compComp'_term| progress rewrite ?instId_elim| progress rewrite ?compComp_elim| progress rewrite ?compComp'_elim| progress rewrite ?instId_list| progress rewrite ?compComp_list| progress rewrite ?compComp'_list| progress rewrite ?rinstId_term| progress rewrite ?compRen_term| progress rewrite ?compRen'_term| progress rewrite ?renComp_term| progress rewrite ?renComp'_term| progress rewrite ?renRen_term| progress rewrite ?renRen'_term| progress rewrite ?rinstId_elim| progress rewrite ?compRen_elim| progress rewrite ?compRen'_elim| progress rewrite ?renComp_elim| progress rewrite ?renComp'_elim| progress rewrite ?renRen_elim| progress rewrite ?renRen'_elim| progress rewrite ?rinstId_list| progress rewrite ?compRen_list| progress rewrite ?compRen'_list| progress rewrite ?renComp_list| progress rewrite ?renComp'_list| progress rewrite ?renRen_list| progress rewrite ?renRen'_list| progress rewrite ?varL_elim| progress rewrite ?varLRen_elim| progress (unfold up_ren, upRen_elim_elim, up_elim_elim)| progress (cbn [subst_term subst_elim subst_list ren_term ren_elim ren_list])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_term in *| progress rewrite ?compComp_term in *| progress rewrite ?compComp'_term in *| progress rewrite ?instId_elim in *| progress rewrite ?compComp_elim in *| progress rewrite ?compComp'_elim in *| progress rewrite ?instId_list in *| progress rewrite ?compComp_list in *| progress rewrite ?compComp'_list in *| progress rewrite ?rinstId_term in *| progress rewrite ?compRen_term in *| progress rewrite ?compRen'_term in *| progress rewrite ?renComp_term in *| progress rewrite ?renComp'_term in *| progress rewrite ?renRen_term in *| progress rewrite ?renRen'_term in *| progress rewrite ?rinstId_elim in *| progress rewrite ?compRen_elim in *| progress rewrite ?compRen'_elim in *| progress rewrite ?renComp_elim in *| progress rewrite ?renComp'_elim in *| progress rewrite ?renRen_elim in *| progress rewrite ?renRen'_elim in *| progress rewrite ?rinstId_list in *| progress rewrite ?compRen_list in *| progress rewrite ?compRen'_list in *| progress rewrite ?renComp_list in *| progress rewrite ?renComp'_list in *| progress rewrite ?renRen_list in *| progress rewrite ?renRen'_list in *| progress rewrite ?varL_elim in *| progress rewrite ?varLRen_elim in *| progress (unfold up_ren, upRen_elim_elim, up_elim_elim in *)| progress (cbn [subst_term subst_elim subst_list ren_term ren_elim ren_list] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_term); try repeat (erewrite rinstInst_elim); try repeat (erewrite rinstInst_list).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_term); try repeat (erewrite <- rinstInst_elim); try repeat (erewrite <- rinstInst_list).
