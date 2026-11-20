module

public import AllFieldMatrices

public section

theorem Gerstenhaber.finrank_adjoin_triple_le :
    ∀ (K : Type*) [Field K] (n : ℕ) (A B C : Matrix (Fin n) (Fin n) K),
      ({A, B, C} : Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute →
        Module.finrank K (Algebra.adjoin K {A, B, C}) ≤ n := by
  intro K _ n A B C h
  have comm (X Y : Matrix (Fin n) (Fin n) K) (hx : X ∈ ({A, B, C} : Set _))
      (hy : Y ∈ ({A, B, C} : Set _)) : Commute X Y := by
    by_cases e : X = Y
    · subst Y
      exact Commute.refl X
    · exact h hx hy e
  exact G3Scalar.field_three_matrices A B C
    (comm A B (by simp) (by simp)) (comm A C (by simp) (by simp))
    (comm B C (by simp) (by simp))

#print axioms Gerstenhaber.finrank_adjoin_triple_le
