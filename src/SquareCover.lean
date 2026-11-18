import BlockIndex
import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.Matrix.Nonsingular
noncomputable section
namespace DivisorG3
open Module LinearMap Submodule Matrix
variable {R W : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup W] [Module R W]
theorem square_cover {r : ℕ} (π : (Fin r → R) →ₗ[R] W) (on : Function.Surjective π)
    (a : R) (ha : a≠0) (ann : ∀ w : W, a • w=0) :
    ∃ P : Matrix (Fin r) (Fin r) R, P.det≠0 ∧ P.mulVecLin.range=π.ker ∧
        ∃ e : QP P ≃ₗ[R] W, ∀ v, e (P.mulVecLin.range.mkQ v)=π v := by
  let F := Fin r → R
  let A := times a F
  have hi : Function.Injective A := by
    intro x y h
    funext i
    exact mul_left_cancel₀ ha (congrFun h i)
  have incl : A.range ≤ π.ker := by
    rintro _ ⟨v,rfl⟩
    change π (a • v)=0
    rw [map_smul,ann]
  have dim : finrank R (LinearMap.ker π)=r := by
    have l := Submodule.finrank_mono incl
    rw [LinearMap.finrank_range_of_inj hi] at l
    have h := Submodule.finrank_le π.ker
    simpa [F] using le_antisymm h l
  let basis := Module.finBasisOfFinrankEq R (LinearMap.ker π) dim
  let f := π.ker.subtype.comp basis.equivFun.symm.toLinearMap
  let P := LinearMap.toMatrix' f
  have hf : P.mulVecLin=f := LinearMap.ext fun v => f.toMatrix'_mulVec v
  have his : Function.Injective P.mulVec := by
    change Function.Injective P.mulVecLin
    rw [hf]; exact π.ker.subtype_injective.comp basis.equivFun.symm.injective
  have ran : P.mulVecLin.range=π.ker := by
    rw [hf,show f=π.ker.subtype.comp basis.equivFun.symm.toLinearMap from rfl,LinearMap.range_comp,
      LinearEquiv.range,Submodule.map_top,Submodule.range_subtype]
  exact ⟨P,Matrix.nonsingular_iff_det_ne_zero.mp (.of_linearIndependent_col (Matrix.mulVec_injective_iff.mp his)),
    ran,(Submodule.quotEquivOfEq _ _ ran) ≪≫ₗ π.quotKerEquivOfSurjective on,fun _ => rfl⟩
#print axioms square_cover
end DivisorG3
