From bidirectional.loose Require Export syntax.

(** Simple types *)
Inductive ty := base | arr (A B: ty).

(** A context *)
Definition ctx n := fin n -> ty.

(** Typing predicate *)
Inductive has_btype {n} (Gamma : ctx n) : bidtm n -> ty -> Prop :=
| ty_lam (A B : ty) (P : bidtm (S n)) :
    @has_btype (S n) (A .: Gamma) P B ->
    has_btype Gamma (lam P) (arr A B)
| ty_app (A : ty) (E : elim (n)) :
    has_etype Gamma E A ->
    has_btype Gamma (app E) A
    
with has_etype {n} (Gamma : ctx n) : elim n -> ty -> Prop :=
| ty_var_elim (x : fin n) :
    has_etype Gamma (var_elim x) (Gamma x)
| ty_hd (A : ty) (P : bidtm (n)) :
    has_btype Gamma P A ->
    has_etype Gamma (hd P) A
| ty_eapp (A B : ty) (E : elim (n)) (Q : bidtm n) :
    has_etype Gamma E (arr A B) ->
    has_btype Gamma Q A ->
    has_etype Gamma (eapp E Q) B.

Notation "Gamma |- P : A" := (has_btype Gamma P A) (at level 20, P at level 99).
Notation "Gamma /- E : A" := (has_etype Gamma E A) (at level 19, E at level 99).

(** Context renaming *)
Definition ltc {k k'} (Gamma: ctx k) (Delta: ctx k') rho := forall x, Delta (rho x) = Gamma x.

(** Context renaming lemma *)
Lemma typing_ren :
  (forall n k (Gamma: ctx n) (Delta: ctx k) (rho: fin n -> fin k) (P: bidtm n) A,
  ltc Gamma Delta rho  -> Gamma |- P : A ->  Delta |- (ren_bidtm rho P) : A) /\
  (forall n k (Gamma: ctx n) (Delta: ctx k) (rho: fin n -> fin k) (E: elim n) A,
  ltc Gamma Delta rho  -> Gamma /- E : A ->  Delta /- (ren_elim rho E) : A).
Proof.
  appl
  intros C H. revert k Delta rho C. induction H; intros; cbn; eauto using has_type.
  - unfold ltc in C. rewrite <- C. constructor.
  - constructor. apply IHhas_type. asimpl. unfold ltc. auto_case.
  - econstructor; eauto.
Qed.
