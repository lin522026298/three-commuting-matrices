import JordanMatrix

noncomputable section
open Module Matrix JordanPrimitive
namespace ActualJordan
variable {K : Type*} [Field K] {n : ℕ}

/-- No input partition, no pre-existing Jordan basis, over an arbitrary field,
including n=0. The returned matrix is genuinely invertible. -/
theorem matrix_from_linear_model (U : Matrix (Fin n) (Fin n) K)
    {H : ℕ} (m : Fin H → ℕ) (a : V K m ≃ₗ[K] (Fin n → K))
    (ha : ∀ v, Matrix.toLinAlgEquiv' U (a v) = a (J m v)) :
    ∃ (e : Ix m ≃ Fin n)
      (G : Matrix (Ix m) (Ix m) K),
      IsUnit G ∧ (U.submatrix e e) * G = G * matrixJ m := by
  classical
  let T : Module.End K (Fin n → K) := Matrix.toLinAlgEquiv' U
  have hc : Fintype.card (Ix m) = n := by
    rw [← Module.finrank_eq_card_basis (coordBasis (K:=K) m),a.finrank_eq]
    simp
  let e : Ix m ≃ Fin n := Fintype.equivFinOfCardEq hc
  let b := (Pi.basisFun K (Fin n)).reindex e.symm
  let v := coordBasis (K:=K) m
  let G := LinearMap.toMatrix v b a.toLinearMap
  let D := LinearMap.toMatrix b v a.symm.toLinearMap
  have hGD : G*D=1 := by
    dsimp [G,D]
    rw [← LinearMap.toMatrix_comp]
    simp
  have hDG : D*G=1 := by
    dsimp [G,D]
    rw [← LinearMap.toMatrix_comp]
    simp
  have hU : LinearMap.toMatrix b b T = U.submatrix e e := by
    ext i j
    simp [LinearMap.toMatrix_apply,b,Basis.reindex_apply,
      T,Matrix.toLinAlgEquiv'_apply,Pi.basisFun_apply,Pi.basisFun_repr]
  refine ⟨e,G,⟨⟨G,D,hGD,hDG⟩,rfl⟩,?_⟩
  have he : T.comp a.toLinearMap = a.toLinearMap.comp (J m) := LinearMap.ext ha
  have hm := congrArg (LinearMap.toMatrix v b) he
  rw [LinearMap.toMatrix_comp v b b,LinearMap.toMatrix_comp v v b,hU] at hm
  exact hm

end ActualJordan
#print axioms ActualJordan.matrix_from_linear_model
