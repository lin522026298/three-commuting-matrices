import JordanActualMatrix
import JordanMultiplicity

noncomputable section
open Module Matrix JordanPrimitive
namespace ActualJordan
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {H : ℕ} (m : Fin H → ℕ)
def identifiedKernel (T : Module.End K M) (a : V K m ≃ₗ[K] M)
    (ha : ∀ v, T (a v) = a (J m v)) : LinearMap.ker (J (K:=K) m) ≃ₗ[K] LinearMap.ker T where
  toFun x := ⟨a x.1,by change T _=0; rw [ha,x.2,map_zero]⟩
  invFun x := ⟨a.symm x,by
    apply a.injective
    change a ((J m) (a.symm _)) = a 0
    rw [← ha,a.apply_symm_apply,x.2,map_zero]⟩
  left_inv x := Subtype.ext (a.symm_apply_apply _)
  right_inv x := Subtype.ext (a.apply_symm_apply _)
  map_add' x y := Subtype.ext (a.map_add _ _)
  map_smul' x y := Subtype.ext (a.map_smul _ _)

variable {n : ℕ}
theorem exists_matrix_jordan_with_nullity (U : Matrix (Fin n) (Fin n) K) (hn : IsNilpotent U) :
    ∃ (H : ℕ) (m : Fin H → ℕ) (e : Ix m ≃ Fin n) (G : Matrix (Ix m) (Ix m) K),
      IsUnit G ∧ (U.submatrix e e)*G=G*matrixJ m ∧
      finrank K (LinearMap.ker (Matrix.toLinAlgEquiv' U)) = ∑ h, m h := by
  obtain ⟨H,m,a,ha⟩ := exists_grouped (Matrix.toLinAlgEquiv' U) (hn.map Matrix.toLinAlgEquiv')
  obtain ⟨e,G,hG,hi⟩ := matrix_from_linear_model U m a ha
  refine ⟨H,m,e,G,hG,hi,?_⟩
  rw [← (identifiedKernel m _ a ha).finrank_eq]
  exact number_of_blocks_is_nullity m

end ActualJordan
#print axioms ActualJordan.exists_matrix_jordan_with_nullity
