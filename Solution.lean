module

public import CharZeroMatrices

public section

theorem Gerstenhaber.charZero_three_commuting_matrices {K : Type*} [Field K] [CharZero K]
    {n : ℕ} (A B C : Matrix (Fin n) (Fin n) K)
    (hAB : Commute A B) (hAC : Commute A C) (hBC : Commute B C) :
    Module.finrank K (Algebra.adjoin K ({A, B, C} : Set (Matrix (Fin n) (Fin n) K))) ≤ n :=
  G3Scalar.charZero_three_matrices A B C hAB hAC hBC

#print axioms Gerstenhaber.charZero_three_commuting_matrices
