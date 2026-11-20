module

public import JordanGroupedModel
public import MatrixOfLinearModel

@[expose] public section

noncomputable section
open Module Matrix JordanPrimitive
namespace ActualJordan
variable {K : Type*} [Field K] {n : ℕ}

/-- No input partition, no pre-existing Jordan basis, over an arbitrary field,
including n=0. The returned matrix is genuinely invertible. -/
theorem exists_matrix_jordan (U : Matrix (Fin n) (Fin n) K) (hn : IsNilpotent U) :
    ∃ (H : ℕ) (m : Fin H → ℕ) (e : Ix m ≃ Fin n)
      (G : Matrix (Ix m) (Ix m) K),
      IsUnit G ∧ (U.submatrix e e) * G = G * matrixJ m := by
  obtain ⟨H,m,a,ha⟩ := exists_grouped (Matrix.toLinAlgEquiv' U) (hn.map Matrix.toLinAlgEquiv')
  obtain ⟨e,G,hG,hi⟩ := matrix_from_linear_model U m a ha
  exact ⟨H,m,e,G,hG,hi⟩
end ActualJordan
#print axioms ActualJordan.exists_matrix_jordan
