Section Relation_Definition.

  Variable A : Type.

  Definition relation := A -> A -> Prop.

  Variable R R1 R2 : relation.

  Section General_Properties_of_Relations.

    Definition reflexive : Prop := forall x:A, R x x.
    Definition transitive : Prop := forall x y z:A, R x y -> R y z -> R x z.
    Definition symmetric : Prop := forall x y:A, R x y -> R y x.
    Definition antisymmetric : Prop := forall x y:A, R x y -> R y x -> x = y.
    
    Definition equiv := reflexive /\ transitive /\ symmetric.

    Definition union (x y : A) := R1 x y \/ R2 x y.

    Inductive clos_refl_trans (x:A) : A -> Prop :=
    | rt_step (y:A) : R x y -> clos_refl_trans x y
    | rt_refl : clos_refl_trans x x
    | rt_trans (y z:A) :
      clos_refl_trans x y -> clos_refl_trans y z -> clos_refl_trans x z.
    
    Inductive clos_refl_trans_1n (x: A) : A -> Prop :=
    | rt1n_refl : clos_refl_trans_1n x x
    | rt1n_trans (y z:A) :
      R x y -> clos_refl_trans_1n y z -> clos_refl_trans_1n x z.    
    
  End General_Properties_of_Relations.
  
End Relation_Definition.

Section Transitivity.

  Variable A : Type.
  Variable R : relation A.
    
  Proposition singlestep_trans x y :
    R x y -> clos_refl_trans_1n _ R x y.
  Proof.
    intro H.
    apply rt1n_trans with y.
    - assumption.
    - constructor.
  Qed.

  Proposition multistep_trans x y z:
    clos_refl_trans_1n _ R x y ->
    clos_refl_trans_1n _ R y z ->
    clos_refl_trans_1n _ R x z.
  Proof.                             
    intros Hxy Hyz.
    induction Hxy.
    - assumption.
    - econstructor ; eauto.
  Qed.

  Proposition crt_equals_crt1n x y :
    clos_refl_trans _ R x y <-> clos_refl_trans_1n _ R x y.
  Proof.
    split.
    - induction 1.
      + now apply singlestep_trans.
      + constructor.
      + now apply multistep_trans with y.
    - induction 1.
      + apply rt_refl.
      + apply rt_trans with y.
        * now constructor.
        * assumption.
  Qed.
  
End Transitivity.

Section Diamond.
  
  Variable T : Type.
  Variable step : relation T.

  Definition diamond step : Prop :=
    forall (t t1 t2: T),
      step t t1 /\ step t t2 ->
      exists t', step t1 t' /\ step t2 t'.
    
End Diamond.
