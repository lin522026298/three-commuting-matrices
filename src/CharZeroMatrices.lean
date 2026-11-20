module

public import AllFieldMatrices

@[expose] public section

namespace G3Scalar

theorem charZero_small (k : Type) [Field k] [CharZero k] (n : ℕ)
    (A : Fin 3 → Matrix (Fin n) (Fin n) k) (hc : ∀ i j, Commute (A i) (A j)) :
    Module.finrank k (Algebra.adjoin k (Set.range A)) ≤ n :=
  field_small k n A hc

theorem charZero_triple_bound (k : Type*) [Field k] [CharZero k] (n : ℕ)
    (A : Fin 3 → Matrix (Fin n) (Fin n) k) (hc : ∀ i j, Commute (A i) (A j)) :
    Module.finrank k (Algebra.adjoin k (Set.range A)) ≤ n :=
  field_triple_bound k n A hc

theorem charZero_three_matrices {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (X Y Z : Matrix (Fin n) (Fin n) K) (hxy : Commute X Y) (hxz : Commute X Z)
    (hyz : Commute Y Z) : Module.finrank K (Algebra.adjoin K ({X,Y,Z} : Set _)) ≤ n :=
  field_three_matrices X Y Z hxy hxz hyz

#print axioms charZero_three_matrices
end G3Scalar
