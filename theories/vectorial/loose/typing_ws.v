From headers Require Export types.

From vectorial.loose Require Export syntax_ws.
  
Inductive typing {n} (Gamma: ctx n) : term n -> type -> Prop := 
| right (t: term (S n)) (A B: type) :
  typing (A .: Gamma) t B ->
  typing Gamma (lam t) (arr A B)

| contr (x: fin n) (l: list n) (A B: type) :
  Gamma x = A -> ltyping Gamma l A B ->
  typing Gamma (der x l) B

| cut_rule (t: term n) (l: list n) (A B: type) :
  typing Gamma t A -> ltyping Gamma l A B ->
  typing Gamma (cut t l) B
         
with ltyping {n} (Gamma: ctx n) : list n -> type -> type -> Prop :=
| lax (B: type) :
  ltyping Gamma nil B B

| left (u: term n) (l: list n) (A B C: type) :
  typing Gamma u A -> ltyping Gamma l B C ->
  ltyping Gamma (cons u l) (arr A B) C.

Scheme sim_typing_ind := Induction for typing Sort Prop
  with sim_ltyping_ind := Induction for ltyping Sort Prop.

Combined Scheme mut_typing_ind from sim_typing_ind, sim_ltyping_ind.
