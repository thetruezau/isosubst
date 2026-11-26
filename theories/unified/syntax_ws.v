From headers Require Export fintype.



Section termelimlist.
Inductive term (nelim : nat) : Type :=
  | lam : term  ((S) nelim) -> term (nelim)
  | mapp : elim  (nelim) -> list  (nelim) -> term (nelim)
 with elim (nelim : nat) : Type :=
  | var_elim : (fin) (nelim) -> elim (nelim)
  | hd : term  (nelim) -> elim (nelim)
  | eapp : elim  (nelim) -> term  (nelim) -> elim (nelim)
 with list (nelim : nat) : Type :=
  | nil : list (nelim)
  | cons : term  (nelim) -> list  (nelim) -> list (nelim).

Lemma congr_lam { melim : nat } { s0 : term  ((S) melim) } { t0 : term  ((S) melim) } (H1 : s0 = t0) : lam (melim) s0 = lam (melim) t0 .
Proof. congruence. Qed.

Lemma congr_mapp { melim : nat } { s0 : elim  (melim) } { s1 : list  (melim) } { t0 : elim  (melim) } { t1 : list  (melim) } (H1 : s0 = t0) (H2 : s1 = t1) : mapp (melim) s0 s1 = mapp (melim) t0 t1 .
Proof. congruence. Qed.

Lemma congr_hd { melim : nat } { s0 : term  (melim) } { t0 : term  (melim) } (H1 : s0 = t0) : hd (melim) s0 = hd (melim) t0 .
Proof. congruence. Qed.

Lemma congr_eapp { melim : nat } { s0 : elim  (melim) } { s1 : term  (melim) } { t0 : elim  (melim) } { t1 : term  (melim) } (H1 : s0 = t0) (H2 : s1 = t1) : eapp (melim) s0 s1 = eapp (melim) t0 t1 .
Proof. congruence. Qed.

Lemma congr_nil { melim : nat } : nil (melim) = nil (melim) .
Proof. congruence. Qed.

Lemma congr_cons { melim : nat } { s0 : term  (melim) } { s1 : list  (melim) } { t0 : term  (melim) } { t1 : list  (melim) } (H1 : s0 = t0) (H2 : s1 = t1) : cons (melim) s0 s1 = cons (melim) t0 t1 .
Proof. congruence. Qed.

Definition upRen_elim_elim { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) : (fin) ((S) (m)) -> (fin) ((S) (n)) :=
  (up_ren) xi.

Fixpoint ren_term { melim : nat } { nelim : nat } (xielim : (fin) (melim) -> (fin) (nelim)) (s : term (melim)) : term (nelim) :=
    match s return term (nelim) with
    | lam (_) s0 => lam (nelim) ((ren_term (upRen_elim_elim xielim)) s0)
    | mapp (_) s0 s1 => mapp (nelim) ((ren_elim xielim) s0) ((ren_list xielim) s1)
    end
 with ren_elim { melim : nat } { nelim : nat } (xielim : (fin) (melim) -> (fin) (nelim)) (s : elim (melim)) : elim (nelim) :=
    match s return elim (nelim) with
    | var_elim (_) s => (var_elim (nelim)) (xielim s)
    | hd (_) s0 => hd (nelim) ((ren_term xielim) s0)
    | eapp (_) s0 s1 => eapp (nelim) ((ren_elim xielim) s0) ((ren_term xielim) s1)
    end
 with ren_list { melim : nat } { nelim : nat } (xielim : (fin) (melim) -> (fin) (nelim)) (s : list (melim)) : list (nelim) :=
    match s return list (nelim) with
    | nil (_)  => nil (nelim)
    | cons (_) s0 s1 => cons (nelim) ((ren_term xielim) s0) ((ren_list xielim) s1)
    end.

Definition up_elim_elim { m : nat } { nelim : nat } (sigma : (fin) (m) -> elim (nelim)) : (fin) ((S) (m)) -> elim ((S) nelim) :=
  (scons) ((var_elim ((S) nelim)) (var_zero)) ((funcomp) (ren_elim (shift)) sigma).

Fixpoint subst_term { melim : nat } { nelim : nat } (sigmaelim : (fin) (melim) -> elim (nelim)) (s : term (melim)) : term (nelim) :=
    match s return term (nelim) with
    | lam (_) s0 => lam (nelim) ((subst_term (up_elim_elim sigmaelim)) s0)
    | mapp (_) s0 s1 => mapp (nelim) ((subst_elim sigmaelim) s0) ((subst_list sigmaelim) s1)
    end
 with subst_elim { melim : nat } { nelim : nat } (sigmaelim : (fin) (melim) -> elim (nelim)) (s : elim (melim)) : elim (nelim) :=
    match s return elim (nelim) with
    | var_elim (_) s => sigmaelim s
    | hd (_) s0 => hd (nelim) ((subst_term sigmaelim) s0)
    | eapp (_) s0 s1 => eapp (nelim) ((subst_elim sigmaelim) s0) ((subst_term sigmaelim) s1)
    end
 with subst_list { melim : nat } { nelim : nat } (sigmaelim : (fin) (melim) -> elim (nelim)) (s : list (melim)) : list (nelim) :=
    match s return list (nelim) with
    | nil (_)  => nil (nelim)
    | cons (_) s0 s1 => cons (nelim) ((subst_term sigmaelim) s0) ((subst_list sigmaelim) s1)
    end.

Definition upId_elim_elim { melim : nat } (sigma : (fin) (melim) -> elim (melim)) (Eq : forall x, sigma x = (var_elim (melim)) x) : forall x, (up_elim_elim sigma) x = (var_elim ((S) melim)) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_elim (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint idSubst_term { melim : nat } (sigmaelim : (fin) (melim) -> elim (melim)) (Eqelim : forall x, sigmaelim x = (var_elim (melim)) x) (s : term (melim)) : subst_term sigmaelim s = s :=
    match s return subst_term sigmaelim s = s with
    | lam (_) s0 => congr_lam ((idSubst_term (up_elim_elim sigmaelim) (upId_elim_elim (_) Eqelim)) s0)
    | mapp (_) s0 s1 => congr_mapp ((idSubst_elim sigmaelim Eqelim) s0) ((idSubst_list sigmaelim Eqelim) s1)
    end
 with idSubst_elim { melim : nat } (sigmaelim : (fin) (melim) -> elim (melim)) (Eqelim : forall x, sigmaelim x = (var_elim (melim)) x) (s : elim (melim)) : subst_elim sigmaelim s = s :=
    match s return subst_elim sigmaelim s = s with
    | var_elim (_) s => Eqelim s
    | hd (_) s0 => congr_hd ((idSubst_term sigmaelim Eqelim) s0)
    | eapp (_) s0 s1 => congr_eapp ((idSubst_elim sigmaelim Eqelim) s0) ((idSubst_term sigmaelim Eqelim) s1)
    end
 with idSubst_list { melim : nat } (sigmaelim : (fin) (melim) -> elim (melim)) (Eqelim : forall x, sigmaelim x = (var_elim (melim)) x) (s : list (melim)) : subst_list sigmaelim s = s :=
    match s return subst_list sigmaelim s = s with
    | nil (_)  => congr_nil 
    | cons (_) s0 s1 => congr_cons ((idSubst_term sigmaelim Eqelim) s0) ((idSubst_list sigmaelim Eqelim) s1)
    end.

Definition upExtRen_elim_elim { m : nat } { n : nat } (xi : (fin) (m) -> (fin) (n)) (zeta : (fin) (m) -> (fin) (n)) (Eq : forall x, xi x = zeta x) : forall x, (upRen_elim_elim xi) x = (upRen_elim_elim zeta) x :=
  fun n => match n with
  | Some fin_n => (ap) (shift) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint extRen_term { melim : nat } { nelim : nat } (xielim : (fin) (melim) -> (fin) (nelim)) (zetaelim : (fin) (melim) -> (fin) (nelim)) (Eqelim : forall x, xielim x = zetaelim x) (s : term (melim)) : ren_term xielim s = ren_term zetaelim s :=
    match s return ren_term xielim s = ren_term zetaelim s with
    | lam (_) s0 => congr_lam ((extRen_term (upRen_elim_elim xielim) (upRen_elim_elim zetaelim) (upExtRen_elim_elim (_) (_) Eqelim)) s0)
    | mapp (_) s0 s1 => congr_mapp ((extRen_elim xielim zetaelim Eqelim) s0) ((extRen_list xielim zetaelim Eqelim) s1)
    end
 with extRen_elim { melim : nat } { nelim : nat } (xielim : (fin) (melim) -> (fin) (nelim)) (zetaelim : (fin) (melim) -> (fin) (nelim)) (Eqelim : forall x, xielim x = zetaelim x) (s : elim (melim)) : ren_elim xielim s = ren_elim zetaelim s :=
    match s return ren_elim xielim s = ren_elim zetaelim s with
    | var_elim (_) s => (ap) (var_elim (nelim)) (Eqelim s)
    | hd (_) s0 => congr_hd ((extRen_term xielim zetaelim Eqelim) s0)
    | eapp (_) s0 s1 => congr_eapp ((extRen_elim xielim zetaelim Eqelim) s0) ((extRen_term xielim zetaelim Eqelim) s1)
    end
 with extRen_list { melim : nat } { nelim : nat } (xielim : (fin) (melim) -> (fin) (nelim)) (zetaelim : (fin) (melim) -> (fin) (nelim)) (Eqelim : forall x, xielim x = zetaelim x) (s : list (melim)) : ren_list xielim s = ren_list zetaelim s :=
    match s return ren_list xielim s = ren_list zetaelim s with
    | nil (_)  => congr_nil 
    | cons (_) s0 s1 => congr_cons ((extRen_term xielim zetaelim Eqelim) s0) ((extRen_list xielim zetaelim Eqelim) s1)
    end.

Definition upExt_elim_elim { m : nat } { nelim : nat } (sigma : (fin) (m) -> elim (nelim)) (tau : (fin) (m) -> elim (nelim)) (Eq : forall x, sigma x = tau x) : forall x, (up_elim_elim sigma) x = (up_elim_elim tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_elim (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint ext_term { melim : nat } { nelim : nat } (sigmaelim : (fin) (melim) -> elim (nelim)) (tauelim : (fin) (melim) -> elim (nelim)) (Eqelim : forall x, sigmaelim x = tauelim x) (s : term (melim)) : subst_term sigmaelim s = subst_term tauelim s :=
    match s return subst_term sigmaelim s = subst_term tauelim s with
    | lam (_) s0 => congr_lam ((ext_term (up_elim_elim sigmaelim) (up_elim_elim tauelim) (upExt_elim_elim (_) (_) Eqelim)) s0)
    | mapp (_) s0 s1 => congr_mapp ((ext_elim sigmaelim tauelim Eqelim) s0) ((ext_list sigmaelim tauelim Eqelim) s1)
    end
 with ext_elim { melim : nat } { nelim : nat } (sigmaelim : (fin) (melim) -> elim (nelim)) (tauelim : (fin) (melim) -> elim (nelim)) (Eqelim : forall x, sigmaelim x = tauelim x) (s : elim (melim)) : subst_elim sigmaelim s = subst_elim tauelim s :=
    match s return subst_elim sigmaelim s = subst_elim tauelim s with
    | var_elim (_) s => Eqelim s
    | hd (_) s0 => congr_hd ((ext_term sigmaelim tauelim Eqelim) s0)
    | eapp (_) s0 s1 => congr_eapp ((ext_elim sigmaelim tauelim Eqelim) s0) ((ext_term sigmaelim tauelim Eqelim) s1)
    end
 with ext_list { melim : nat } { nelim : nat } (sigmaelim : (fin) (melim) -> elim (nelim)) (tauelim : (fin) (melim) -> elim (nelim)) (Eqelim : forall x, sigmaelim x = tauelim x) (s : list (melim)) : subst_list sigmaelim s = subst_list tauelim s :=
    match s return subst_list sigmaelim s = subst_list tauelim s with
    | nil (_)  => congr_nil 
    | cons (_) s0 s1 => congr_cons ((ext_term sigmaelim tauelim Eqelim) s0) ((ext_list sigmaelim tauelim Eqelim) s1)
    end.

Definition up_ren_ren_elim_elim { k : nat } { l : nat } { m : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> (fin) (m)) (theta : (fin) (k) -> (fin) (m)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_elim_elim tau) (upRen_elim_elim xi)) x = (upRen_elim_elim theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_term { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) (rhoelim : (fin) (melim) -> (fin) (lelim)) (Eqelim : forall x, ((funcomp) zetaelim xielim) x = rhoelim x) (s : term (melim)) : ren_term zetaelim (ren_term xielim s) = ren_term rhoelim s :=
    match s return ren_term zetaelim (ren_term xielim s) = ren_term rhoelim s with
    | lam (_) s0 => congr_lam ((compRenRen_term (upRen_elim_elim xielim) (upRen_elim_elim zetaelim) (upRen_elim_elim rhoelim) (up_ren_ren (_) (_) (_) Eqelim)) s0)
    | mapp (_) s0 s1 => congr_mapp ((compRenRen_elim xielim zetaelim rhoelim Eqelim) s0) ((compRenRen_list xielim zetaelim rhoelim Eqelim) s1)
    end
 with compRenRen_elim { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) (rhoelim : (fin) (melim) -> (fin) (lelim)) (Eqelim : forall x, ((funcomp) zetaelim xielim) x = rhoelim x) (s : elim (melim)) : ren_elim zetaelim (ren_elim xielim s) = ren_elim rhoelim s :=
    match s return ren_elim zetaelim (ren_elim xielim s) = ren_elim rhoelim s with
    | var_elim (_) s => (ap) (var_elim (lelim)) (Eqelim s)
    | hd (_) s0 => congr_hd ((compRenRen_term xielim zetaelim rhoelim Eqelim) s0)
    | eapp (_) s0 s1 => congr_eapp ((compRenRen_elim xielim zetaelim rhoelim Eqelim) s0) ((compRenRen_term xielim zetaelim rhoelim Eqelim) s1)
    end
 with compRenRen_list { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) (rhoelim : (fin) (melim) -> (fin) (lelim)) (Eqelim : forall x, ((funcomp) zetaelim xielim) x = rhoelim x) (s : list (melim)) : ren_list zetaelim (ren_list xielim s) = ren_list rhoelim s :=
    match s return ren_list zetaelim (ren_list xielim s) = ren_list rhoelim s with
    | nil (_)  => congr_nil 
    | cons (_) s0 s1 => congr_cons ((compRenRen_term xielim zetaelim rhoelim Eqelim) s0) ((compRenRen_list xielim zetaelim rhoelim Eqelim) s1)
    end.

Definition up_ren_subst_elim_elim { k : nat } { l : nat } { melim : nat } (xi : (fin) (k) -> (fin) (l)) (tau : (fin) (l) -> elim (melim)) (theta : (fin) (k) -> elim (melim)) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_elim_elim tau) (upRen_elim_elim xi)) x = (up_elim_elim theta) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_elim (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint compRenSubst_term { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) (thetaelim : (fin) (melim) -> elim (lelim)) (Eqelim : forall x, ((funcomp) tauelim xielim) x = thetaelim x) (s : term (melim)) : subst_term tauelim (ren_term xielim s) = subst_term thetaelim s :=
    match s return subst_term tauelim (ren_term xielim s) = subst_term thetaelim s with
    | lam (_) s0 => congr_lam ((compRenSubst_term (upRen_elim_elim xielim) (up_elim_elim tauelim) (up_elim_elim thetaelim) (up_ren_subst_elim_elim (_) (_) (_) Eqelim)) s0)
    | mapp (_) s0 s1 => congr_mapp ((compRenSubst_elim xielim tauelim thetaelim Eqelim) s0) ((compRenSubst_list xielim tauelim thetaelim Eqelim) s1)
    end
 with compRenSubst_elim { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) (thetaelim : (fin) (melim) -> elim (lelim)) (Eqelim : forall x, ((funcomp) tauelim xielim) x = thetaelim x) (s : elim (melim)) : subst_elim tauelim (ren_elim xielim s) = subst_elim thetaelim s :=
    match s return subst_elim tauelim (ren_elim xielim s) = subst_elim thetaelim s with
    | var_elim (_) s => Eqelim s
    | hd (_) s0 => congr_hd ((compRenSubst_term xielim tauelim thetaelim Eqelim) s0)
    | eapp (_) s0 s1 => congr_eapp ((compRenSubst_elim xielim tauelim thetaelim Eqelim) s0) ((compRenSubst_term xielim tauelim thetaelim Eqelim) s1)
    end
 with compRenSubst_list { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) (thetaelim : (fin) (melim) -> elim (lelim)) (Eqelim : forall x, ((funcomp) tauelim xielim) x = thetaelim x) (s : list (melim)) : subst_list tauelim (ren_list xielim s) = subst_list thetaelim s :=
    match s return subst_list tauelim (ren_list xielim s) = subst_list thetaelim s with
    | nil (_)  => congr_nil 
    | cons (_) s0 s1 => congr_cons ((compRenSubst_term xielim tauelim thetaelim Eqelim) s0) ((compRenSubst_list xielim tauelim thetaelim Eqelim) s1)
    end.

Definition up_subst_ren_elim_elim { k : nat } { lelim : nat } { melim : nat } (sigma : (fin) (k) -> elim (lelim)) (zetaelim : (fin) (lelim) -> (fin) (melim)) (theta : (fin) (k) -> elim (melim)) (Eq : forall x, ((funcomp) (ren_elim zetaelim) sigma) x = theta x) : forall x, ((funcomp) (ren_elim (upRen_elim_elim zetaelim)) (up_elim_elim sigma)) x = (up_elim_elim theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenRen_elim (shift) (upRen_elim_elim zetaelim) ((funcomp) (shift) zetaelim) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_elim zetaelim (shift) ((funcomp) (shift) zetaelim) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_elim (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstRen_term { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) (thetaelim : (fin) (melim) -> elim (lelim)) (Eqelim : forall x, ((funcomp) (ren_elim zetaelim) sigmaelim) x = thetaelim x) (s : term (melim)) : ren_term zetaelim (subst_term sigmaelim s) = subst_term thetaelim s :=
    match s return ren_term zetaelim (subst_term sigmaelim s) = subst_term thetaelim s with
    | lam (_) s0 => congr_lam ((compSubstRen_term (up_elim_elim sigmaelim) (upRen_elim_elim zetaelim) (up_elim_elim thetaelim) (up_subst_ren_elim_elim (_) (_) (_) Eqelim)) s0)
    | mapp (_) s0 s1 => congr_mapp ((compSubstRen_elim sigmaelim zetaelim thetaelim Eqelim) s0) ((compSubstRen_list sigmaelim zetaelim thetaelim Eqelim) s1)
    end
 with compSubstRen_elim { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) (thetaelim : (fin) (melim) -> elim (lelim)) (Eqelim : forall x, ((funcomp) (ren_elim zetaelim) sigmaelim) x = thetaelim x) (s : elim (melim)) : ren_elim zetaelim (subst_elim sigmaelim s) = subst_elim thetaelim s :=
    match s return ren_elim zetaelim (subst_elim sigmaelim s) = subst_elim thetaelim s with
    | var_elim (_) s => Eqelim s
    | hd (_) s0 => congr_hd ((compSubstRen_term sigmaelim zetaelim thetaelim Eqelim) s0)
    | eapp (_) s0 s1 => congr_eapp ((compSubstRen_elim sigmaelim zetaelim thetaelim Eqelim) s0) ((compSubstRen_term sigmaelim zetaelim thetaelim Eqelim) s1)
    end
 with compSubstRen_list { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) (thetaelim : (fin) (melim) -> elim (lelim)) (Eqelim : forall x, ((funcomp) (ren_elim zetaelim) sigmaelim) x = thetaelim x) (s : list (melim)) : ren_list zetaelim (subst_list sigmaelim s) = subst_list thetaelim s :=
    match s return ren_list zetaelim (subst_list sigmaelim s) = subst_list thetaelim s with
    | nil (_)  => congr_nil 
    | cons (_) s0 s1 => congr_cons ((compSubstRen_term sigmaelim zetaelim thetaelim Eqelim) s0) ((compSubstRen_list sigmaelim zetaelim thetaelim Eqelim) s1)
    end.

Definition up_subst_subst_elim_elim { k : nat } { lelim : nat } { melim : nat } (sigma : (fin) (k) -> elim (lelim)) (tauelim : (fin) (lelim) -> elim (melim)) (theta : (fin) (k) -> elim (melim)) (Eq : forall x, ((funcomp) (subst_elim tauelim) sigma) x = theta x) : forall x, ((funcomp) (subst_elim (up_elim_elim tauelim)) (up_elim_elim sigma)) x = (up_elim_elim theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compRenSubst_elim (shift) (up_elim_elim tauelim) ((funcomp) (up_elim_elim tauelim) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_elim tauelim (shift) ((funcomp) (ren_elim (shift)) tauelim) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_elim (shift)) (Eq fin_n)))
  | None  => eq_refl
  end.

Fixpoint compSubstSubst_term { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) (thetaelim : (fin) (melim) -> elim (lelim)) (Eqelim : forall x, ((funcomp) (subst_elim tauelim) sigmaelim) x = thetaelim x) (s : term (melim)) : subst_term tauelim (subst_term sigmaelim s) = subst_term thetaelim s :=
    match s return subst_term tauelim (subst_term sigmaelim s) = subst_term thetaelim s with
    | lam (_) s0 => congr_lam ((compSubstSubst_term (up_elim_elim sigmaelim) (up_elim_elim tauelim) (up_elim_elim thetaelim) (up_subst_subst_elim_elim (_) (_) (_) Eqelim)) s0)
    | mapp (_) s0 s1 => congr_mapp ((compSubstSubst_elim sigmaelim tauelim thetaelim Eqelim) s0) ((compSubstSubst_list sigmaelim tauelim thetaelim Eqelim) s1)
    end
 with compSubstSubst_elim { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) (thetaelim : (fin) (melim) -> elim (lelim)) (Eqelim : forall x, ((funcomp) (subst_elim tauelim) sigmaelim) x = thetaelim x) (s : elim (melim)) : subst_elim tauelim (subst_elim sigmaelim s) = subst_elim thetaelim s :=
    match s return subst_elim tauelim (subst_elim sigmaelim s) = subst_elim thetaelim s with
    | var_elim (_) s => Eqelim s
    | hd (_) s0 => congr_hd ((compSubstSubst_term sigmaelim tauelim thetaelim Eqelim) s0)
    | eapp (_) s0 s1 => congr_eapp ((compSubstSubst_elim sigmaelim tauelim thetaelim Eqelim) s0) ((compSubstSubst_term sigmaelim tauelim thetaelim Eqelim) s1)
    end
 with compSubstSubst_list { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) (thetaelim : (fin) (melim) -> elim (lelim)) (Eqelim : forall x, ((funcomp) (subst_elim tauelim) sigmaelim) x = thetaelim x) (s : list (melim)) : subst_list tauelim (subst_list sigmaelim s) = subst_list thetaelim s :=
    match s return subst_list tauelim (subst_list sigmaelim s) = subst_list thetaelim s with
    | nil (_)  => congr_nil 
    | cons (_) s0 s1 => congr_cons ((compSubstSubst_term sigmaelim tauelim thetaelim Eqelim) s0) ((compSubstSubst_list sigmaelim tauelim thetaelim Eqelim) s1)
    end.

Definition rinstInst_up_elim_elim { m : nat } { nelim : nat } (xi : (fin) (m) -> (fin) (nelim)) (sigma : (fin) (m) -> elim (nelim)) (Eq : forall x, ((funcomp) (var_elim (nelim)) xi) x = sigma x) : forall x, ((funcomp) (var_elim ((S) nelim)) (upRen_elim_elim xi)) x = (up_elim_elim sigma) x :=
  fun n => match n with
  | Some fin_n => (ap) (ren_elim (shift)) (Eq fin_n)
  | None  => eq_refl
  end.

Fixpoint rinst_inst_term { melim : nat } { nelim : nat } (xielim : (fin) (melim) -> (fin) (nelim)) (sigmaelim : (fin) (melim) -> elim (nelim)) (Eqelim : forall x, ((funcomp) (var_elim (nelim)) xielim) x = sigmaelim x) (s : term (melim)) : ren_term xielim s = subst_term sigmaelim s :=
    match s return ren_term xielim s = subst_term sigmaelim s with
    | lam (_) s0 => congr_lam ((rinst_inst_term (upRen_elim_elim xielim) (up_elim_elim sigmaelim) (rinstInst_up_elim_elim (_) (_) Eqelim)) s0)
    | mapp (_) s0 s1 => congr_mapp ((rinst_inst_elim xielim sigmaelim Eqelim) s0) ((rinst_inst_list xielim sigmaelim Eqelim) s1)
    end
 with rinst_inst_elim { melim : nat } { nelim : nat } (xielim : (fin) (melim) -> (fin) (nelim)) (sigmaelim : (fin) (melim) -> elim (nelim)) (Eqelim : forall x, ((funcomp) (var_elim (nelim)) xielim) x = sigmaelim x) (s : elim (melim)) : ren_elim xielim s = subst_elim sigmaelim s :=
    match s return ren_elim xielim s = subst_elim sigmaelim s with
    | var_elim (_) s => Eqelim s
    | hd (_) s0 => congr_hd ((rinst_inst_term xielim sigmaelim Eqelim) s0)
    | eapp (_) s0 s1 => congr_eapp ((rinst_inst_elim xielim sigmaelim Eqelim) s0) ((rinst_inst_term xielim sigmaelim Eqelim) s1)
    end
 with rinst_inst_list { melim : nat } { nelim : nat } (xielim : (fin) (melim) -> (fin) (nelim)) (sigmaelim : (fin) (melim) -> elim (nelim)) (Eqelim : forall x, ((funcomp) (var_elim (nelim)) xielim) x = sigmaelim x) (s : list (melim)) : ren_list xielim s = subst_list sigmaelim s :=
    match s return ren_list xielim s = subst_list sigmaelim s with
    | nil (_)  => congr_nil 
    | cons (_) s0 s1 => congr_cons ((rinst_inst_term xielim sigmaelim Eqelim) s0) ((rinst_inst_list xielim sigmaelim Eqelim) s1)
    end.

Lemma rinstInst_term { melim : nat } { nelim : nat } (xielim : (fin) (melim) -> (fin) (nelim)) : ren_term xielim = subst_term ((funcomp) (var_elim (nelim)) xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_term xielim (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_elim { melim : nat } { nelim : nat } (xielim : (fin) (melim) -> (fin) (nelim)) : ren_elim xielim = subst_elim ((funcomp) (var_elim (nelim)) xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_elim xielim (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_list { melim : nat } { nelim : nat } (xielim : (fin) (melim) -> (fin) (nelim)) : ren_list xielim = subst_list ((funcomp) (var_elim (nelim)) xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_list xielim (_) (fun n => eq_refl) x)). Qed.

Lemma instId_term { melim : nat } : subst_term (var_elim (melim)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_term (var_elim (melim)) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_elim { melim : nat } : subst_elim (var_elim (melim)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_elim (var_elim (melim)) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_list { melim : nat } : subst_list (var_elim (melim)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_list (var_elim (melim)) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_term { melim : nat } : @ren_term (melim) (melim) (id) = id .
Proof. exact ((eq_trans) (rinstInst_term ((id) (_))) instId_term). Qed.

Lemma rinstId_elim { melim : nat } : @ren_elim (melim) (melim) (id) = id .
Proof. exact ((eq_trans) (rinstInst_elim ((id) (_))) instId_elim). Qed.

Lemma rinstId_list { melim : nat } : @ren_list (melim) (melim) (id) = id .
Proof. exact ((eq_trans) (rinstInst_list ((id) (_))) instId_list). Qed.

Lemma varL_elim { melim : nat } { nelim : nat } (sigmaelim : (fin) (melim) -> elim (nelim)) : (funcomp) (subst_elim sigmaelim) (var_elim (melim)) = sigmaelim .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_elim { melim : nat } { nelim : nat } (xielim : (fin) (melim) -> (fin) (nelim)) : (funcomp) (ren_elim xielim) (var_elim (melim)) = (funcomp) (var_elim (nelim)) xielim .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_term { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) (s : term (melim)) : subst_term tauelim (subst_term sigmaelim s) = subst_term ((funcomp) (subst_elim tauelim) sigmaelim) s .
Proof. exact (compSubstSubst_term sigmaelim tauelim (_) (fun n => eq_refl) s). Qed.

Lemma compComp_elim { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) (s : elim (melim)) : subst_elim tauelim (subst_elim sigmaelim s) = subst_elim ((funcomp) (subst_elim tauelim) sigmaelim) s .
Proof. exact (compSubstSubst_elim sigmaelim tauelim (_) (fun n => eq_refl) s). Qed.

Lemma compComp_list { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) (s : list (melim)) : subst_list tauelim (subst_list sigmaelim s) = subst_list ((funcomp) (subst_elim tauelim) sigmaelim) s .
Proof. exact (compSubstSubst_list sigmaelim tauelim (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_term { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) : (funcomp) (subst_term tauelim) (subst_term sigmaelim) = subst_term ((funcomp) (subst_elim tauelim) sigmaelim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_term sigmaelim tauelim n)). Qed.

Lemma compComp'_elim { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) : (funcomp) (subst_elim tauelim) (subst_elim sigmaelim) = subst_elim ((funcomp) (subst_elim tauelim) sigmaelim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_elim sigmaelim tauelim n)). Qed.

Lemma compComp'_list { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) : (funcomp) (subst_list tauelim) (subst_list sigmaelim) = subst_list ((funcomp) (subst_elim tauelim) sigmaelim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_list sigmaelim tauelim n)). Qed.

Lemma compRen_term { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) (s : term (melim)) : ren_term zetaelim (subst_term sigmaelim s) = subst_term ((funcomp) (ren_elim zetaelim) sigmaelim) s .
Proof. exact (compSubstRen_term sigmaelim zetaelim (_) (fun n => eq_refl) s). Qed.

Lemma compRen_elim { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) (s : elim (melim)) : ren_elim zetaelim (subst_elim sigmaelim s) = subst_elim ((funcomp) (ren_elim zetaelim) sigmaelim) s .
Proof. exact (compSubstRen_elim sigmaelim zetaelim (_) (fun n => eq_refl) s). Qed.

Lemma compRen_list { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) (s : list (melim)) : ren_list zetaelim (subst_list sigmaelim s) = subst_list ((funcomp) (ren_elim zetaelim) sigmaelim) s .
Proof. exact (compSubstRen_list sigmaelim zetaelim (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_term { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) : (funcomp) (ren_term zetaelim) (subst_term sigmaelim) = subst_term ((funcomp) (ren_elim zetaelim) sigmaelim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_term sigmaelim zetaelim n)). Qed.

Lemma compRen'_elim { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) : (funcomp) (ren_elim zetaelim) (subst_elim sigmaelim) = subst_elim ((funcomp) (ren_elim zetaelim) sigmaelim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_elim sigmaelim zetaelim n)). Qed.

Lemma compRen'_list { kelim : nat } { lelim : nat } { melim : nat } (sigmaelim : (fin) (melim) -> elim (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) : (funcomp) (ren_list zetaelim) (subst_list sigmaelim) = subst_list ((funcomp) (ren_elim zetaelim) sigmaelim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_list sigmaelim zetaelim n)). Qed.

Lemma renComp_term { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) (s : term (melim)) : subst_term tauelim (ren_term xielim s) = subst_term ((funcomp) tauelim xielim) s .
Proof. exact (compRenSubst_term xielim tauelim (_) (fun n => eq_refl) s). Qed.

Lemma renComp_elim { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) (s : elim (melim)) : subst_elim tauelim (ren_elim xielim s) = subst_elim ((funcomp) tauelim xielim) s .
Proof. exact (compRenSubst_elim xielim tauelim (_) (fun n => eq_refl) s). Qed.

Lemma renComp_list { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) (s : list (melim)) : subst_list tauelim (ren_list xielim s) = subst_list ((funcomp) tauelim xielim) s .
Proof. exact (compRenSubst_list xielim tauelim (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_term { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) : (funcomp) (subst_term tauelim) (ren_term xielim) = subst_term ((funcomp) tauelim xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_term xielim tauelim n)). Qed.

Lemma renComp'_elim { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) : (funcomp) (subst_elim tauelim) (ren_elim xielim) = subst_elim ((funcomp) tauelim xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_elim xielim tauelim n)). Qed.

Lemma renComp'_list { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (tauelim : (fin) (kelim) -> elim (lelim)) : (funcomp) (subst_list tauelim) (ren_list xielim) = subst_list ((funcomp) tauelim xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_list xielim tauelim n)). Qed.

Lemma renRen_term { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) (s : term (melim)) : ren_term zetaelim (ren_term xielim s) = ren_term ((funcomp) zetaelim xielim) s .
Proof. exact (compRenRen_term xielim zetaelim (_) (fun n => eq_refl) s). Qed.

Lemma renRen_elim { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) (s : elim (melim)) : ren_elim zetaelim (ren_elim xielim s) = ren_elim ((funcomp) zetaelim xielim) s .
Proof. exact (compRenRen_elim xielim zetaelim (_) (fun n => eq_refl) s). Qed.

Lemma renRen_list { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) (s : list (melim)) : ren_list zetaelim (ren_list xielim s) = ren_list ((funcomp) zetaelim xielim) s .
Proof. exact (compRenRen_list xielim zetaelim (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_term { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) : (funcomp) (ren_term zetaelim) (ren_term xielim) = ren_term ((funcomp) zetaelim xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_term xielim zetaelim n)). Qed.

Lemma renRen'_elim { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) : (funcomp) (ren_elim zetaelim) (ren_elim xielim) = ren_elim ((funcomp) zetaelim xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_elim xielim zetaelim n)). Qed.

Lemma renRen'_list { kelim : nat } { lelim : nat } { melim : nat } (xielim : (fin) (melim) -> (fin) (kelim)) (zetaelim : (fin) (kelim) -> (fin) (lelim)) : (funcomp) (ren_list zetaelim) (ren_list xielim) = ren_list ((funcomp) zetaelim xielim) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_list xielim zetaelim n)). Qed.

End termelimlist.

Arguments lam {nelim}.

Arguments mapp {nelim}.

Arguments var_elim {nelim}.

Arguments hd {nelim}.

Arguments eapp {nelim}.

Arguments nil {nelim}.

Arguments cons {nelim}.

Global Instance Subst_term { melim : nat } { nelim : nat } : Subst1 ((fin) (melim) -> elim (nelim)) (term (melim)) (term (nelim)) := @subst_term (melim) (nelim) .

Global Instance Subst_elim { melim : nat } { nelim : nat } : Subst1 ((fin) (melim) -> elim (nelim)) (elim (melim)) (elim (nelim)) := @subst_elim (melim) (nelim) .

Global Instance Subst_list { melim : nat } { nelim : nat } : Subst1 ((fin) (melim) -> elim (nelim)) (list (melim)) (list (nelim)) := @subst_list (melim) (nelim) .

Global Instance Ren_term { melim : nat } { nelim : nat } : Ren1 ((fin) (melim) -> (fin) (nelim)) (term (melim)) (term (nelim)) := @ren_term (melim) (nelim) .

Global Instance Ren_elim { melim : nat } { nelim : nat } : Ren1 ((fin) (melim) -> (fin) (nelim)) (elim (melim)) (elim (nelim)) := @ren_elim (melim) (nelim) .

Global Instance Ren_list { melim : nat } { nelim : nat } : Ren1 ((fin) (melim) -> (fin) (nelim)) (list (melim)) (list (nelim)) := @ren_list (melim) (nelim) .

Global Instance VarInstance_elim { melim : nat } : Var ((fin) (melim)) (elim (melim)) := @var_elim (melim) .

Notation "x '__elim'" := (var_elim x) (at level 5, format "x __elim") : subst_scope.

Notation "x '__elim'" := (@ids (_) (_) VarInstance_elim x) (at level 5, only printing, format "x __elim") : subst_scope.

Notation "'var'" := (var_elim) (only printing, at level 1) : subst_scope.

Class Up_elim X Y := up_elim : X -> Y.

Notation "↑__elim" := (up_elim) (only printing) : subst_scope.

Notation "↑__elim" := (up_elim_elim) (only printing) : subst_scope.

Global Instance Up_elim_elim { m : nat } { nelim : nat } : Up_elim (_) (_) := @up_elim_elim (m) (nelim) .

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
