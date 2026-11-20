module

public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

public section

/-!
# The Gerstenhaber problem for three commuting matrices

The three matrices may have any size and entries in any field. The set of
generators can have fewer than three elements if some matrices coincide.
The bound concerns the unital subalgebra they generate over the given field.

The declaration follows the independent Formal Conjectures statement
`Gerstenhaber.finrank_adjoin_triple_le` (revision
`d8d031d4998c78575159ccab9a7a9e95ce043883`).
-/

/-- Three pairwise commuting matrices of size n generate an algebra of dimension at most n. -/
theorem Gerstenhaber.finrank_adjoin_triple_le :
    ∀ (K : Type*) [Field K] (n : ℕ) (A B C : Matrix (Fin n) (Fin n) K),
      ({A, B, C} : Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute →
        Module.finrank K (Algebra.adjoin K {A, B, C}) ≤ n := by
  sorry
