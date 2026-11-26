From headers Require Import fintype.

Inductive type : Type :=
  | base
  | arr (A: type) (B: type).

Definition ctx n := fin n -> type.
