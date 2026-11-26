From headers Require Export relations.

From vectorial.loose Require Export syntax_ws.

Set Implicit Arguments.

Section Compatibilty.

  Variable base : forall n, relation (term n).
  
  Inductive comp {n} : relation (term n) :=
  | comp_der x l l' :
    lcomp l l' ->
    comp (der x l) (der x l')

  | comp_lam (t t': term (S n)) :
    @comp (S n) t t' ->
    comp (lam t) (lam t')

  | comp_cut1 t t' l :
    comp t t' ->
    comp (cut t l) (cut t' l)

  | comp_cut2 t l l' :
    lcomp l l' ->
    comp (cut t l) (cut t l')

  | comp_b t t' :
    base t t' -> comp t t'

  with lcomp {n} : relation (list n) :=
  | lcomp_head u u' l :
    comp u u' ->
    lcomp (cons u l) (cons u' l)

  | lcomp_tail u l l' :
    lcomp l l' ->
    lcomp (cons u l) (cons u l').

  Scheme sim_comp_ind := Induction for comp Sort Prop
    with sim_lcomp_ind := Induction for lcomp Sort Prop.

  Combined Scheme mut_comp_ind from sim_comp_ind, sim_lcomp_ind.
End Compatibilty.

Section IsCompatible.
  Variable R : forall n, relation (term n).
  Variable Rl : forall n, relation (list n).
  
  Record is_compatible {n} := {
      is_comp_der : forall (x: fin n) (l l': list n), Rl l l' -> R (der x l) (der x l') ;
      is_comp_lam : forall (t t': term (S n)), R t t' -> R (lam t) (lam t') ;
      is_comp_cut1 : forall (t t': term n) (l: list n), R t t' -> R (cut t l) (cut t' l) ;
      is_comp_cut2 : forall (t: term n) (l l': list n), Rl l l' -> R (cut t l) (cut t l') ;
      is_comp_head : forall (u u': term n) (l: list n), R u u' -> Rl (cons u l) (cons u' l) ;
      is_comp_tail : forall (u: term n) (l l': list n), Rl l l' -> Rl (cons u l) (cons u l')
    }.
End IsCompatible.
  
(** Definitions of Reduction *)

Inductive beta (n: nat): relation (term n) :=
| base_beta (t: term (S n)) (u t': term n) (l: list n) :
  t' = usubst u t -> beta (cut (lam t) (cons u l)) (cut t' l).

Inductive pi1 (n: nat): relation (term n) :=
| base_pi1 (x: fin n) (l l' l'': list n):
  l'' = l+l' -> pi1 (cut (der x l) l') (der x l'').

Inductive pi2 (n: nat): relation (term n) :=
| base_pi2 t l l' l'':
  l'' = l+l' -> pi2 (cut (cut t l) l') (cut t l'').

Inductive eps (n: nat): relation (term n) :=
| base_eps t : eps (cut t nil) t.

(** Partial step reductions *)

Abbreviation step_beta := (comp beta).
Abbreviation lstep_beta := (lcomp beta).

Definition pi (n: nat) := union _ (@pi1 n) (@pi2 n).
Abbreviation step_pi := (comp pi).
Abbreviation lstep_pi := (lcomp pi).

Abbreviation step_eps := (comp eps).
Abbreviation lstep_eps := (lcomp eps).

Definition pi_eps (n: nat) := union _ (@pi1 n) (@eps n).
Abbreviation step_pi_eps := (comp pi_eps).
Abbreviation lstep_pi_eps := (lcomp pi_eps).

Abbreviation multistep_pi_eps := (clos_refl_trans_1n _ step_pi_eps).
Abbreviation lmultistep_pi_eps := (clos_refl_trans_1n _ lstep_pi_eps).

(** Definition of πε normal forms *)

Definition pi_eps_nf {n} (t: term n) : Prop :=
  ~exists (t': term n), step_pi_eps t t'.
Definition pi_eps_lnf {n} (l: list n) : Prop :=
  ~exists (l': list n), lstep_pi_eps l l'.

(** One step reduction *)

Definition beta_pi_eps (n: nat) := union _ (@beta n) (@pi_eps n).
Abbreviation step := (comp beta_pi_eps).
Abbreviation lstep := (lcomp beta_pi_eps).

(** Multistep reduction *)

Abbreviation multistep := (clos_refl_trans_1n _ step).
Abbreviation lmultistep := (clos_refl_trans_1n _ lstep).
