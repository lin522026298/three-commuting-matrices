import DividedTail
import DVRScalar
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.ToLin
noncomputable section
namespace DivisorG3
open PowerSeries Module LinearMap Submodule
open scoped Matrix
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
abbrev Row (k ι : Type*) := ι → O k
abbrev sq (k ι : Type*) := Matrix ι ι (O k)
def reduceVec (k ι : Type*) [Field k] : Row k ι →ₗ[k] ι → k where
  toFun v i := constantCoeff (v i)
  map_add' v w := by ext; simp
  map_smul' c v := by ext i; change constantCoeff (c • v i) = c * _; rw [PowerSeries.smul_eq_C_mul,map_mul,constantCoeff_C]
omit [Fintype ι] [DecidableEq ι] in
theorem reduceVec_surj : Function.Surjective (reduceVec k ι) := fun u =>
  ⟨fun i => C (u i),funext fun _ => constantCoeff_C _⟩
omit [Fintype ι] [DecidableEq ι] in
theorem reduceVec_ker : (reduceVec k ι).ker = ((times (PowerSeries.X : O k) (Row k ι)).range).restrictScalars k := by
  ext v
  change (fun i => constantCoeff (v i)) = 0 ↔ ∃ w : Row k ι, (fun i => X * w i) = v
  constructor
  · intro h
    choose w hw using fun i => X_dvd_iff.mpr (congrFun h i)
    exact ⟨w,funext fun i => (hw i).symm⟩
  · rintro ⟨v,rfl⟩; funext i; simp
def reduceEquiv : Coker (times (PowerSeries.X : O k) (Row k ι)) ≃ₗ[k] (ι → k) :=
  (Submodule.Quotient.restrictScalarsEquiv k _).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ reduceVec_ker.symm ≪≫ₗ
    (reduceVec k ι).quotKerEquivOfSurjective reduceVec_surj

omit [DecidableEq ι] in
theorem factor_X (P : sq k ι) (hp : ∀ i j, constantCoeff (P i j)=0) :
    ∃ Q : sq k ι, ∀ v, P.mulVecLin v = (PowerSeries.X : O k) • Q.mulVecLin v := by
  choose Q hQ using fun i j => X_dvd_iff.mpr (hp i j)
  refine ⟨Q,fun v => ?_⟩
  have hP : P = (PowerSeries.X : O k) • Q := Matrix.ext fun i j => hQ i j
  rw [hP]
  exact Matrix.smul_mulVec _ _ _

omit [Fintype ι] [DecidableEq ι] in
theorem xReg : Function.Injective (fun v : Row k ι => (PowerSeries.X : O k) • v) := by
  intro v w h
  funext i
  exact mul_left_cancel₀ PowerSeries.X_ne_zero (congrFun h i)

/-- True tail in an arbitrary square integral presentation (no diagonal or rectangular
Jordan type assumption), including the normalization of tail representatives. -/
theorem actual_tail (P : sq k ι) (p : P.det≠0) (p0 : ∀ i j, constantCoeff (P i j)=0) :
    ∃ Q : sq k ι, ∃ e : (ι → k) ≃ₗ[k] Tail (PowerSeries.X : O k) P.mulVecLin,
      (∀ v, P.mulVecLin v = (PowerSeries.X : O k) • Q.mulVecLin v) ∧
      (∀ v, (e (reduceVec k ι v)).val = P.mulVecLin.range.mkQ (Q.mulVecLin v)) ∧
      (∀ Y Y' : sq k ι, Y * P = P * Y' → ∀ v,
        (e (reduceVec k ι (Y'.mulVecLin v))).val = P.mulVecLin.range.mkQ (Y.mulVecLin (Q.mulVecLin v))) := by
  obtain ⟨Q,fac⟩ := factor_X P p0
  let inj := Matrix.mulVec_injective_of_det_ne_zero p
  let z := tailEquiv _ _ _ fac inj xReg
  let e := reduceEquiv.symm ≪≫ₗ z.restrictScalars k
  have h (v) : (e (reduceVec k ι v)).val = P.mulVecLin.range.mkQ (Q.mulVecLin v) := by
    have hr : reduceEquiv ((times (PowerSeries.X : O k) (Row k ι)).range.mkQ v) = reduceVec k ι v := rfl
    rw [←hr]; simp only [e,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
    exact tail_formula _ _ _ fac inj xReg v
  refine ⟨Q,e,fac,h,?_⟩
  intro Y Y' eq v
  rw [h]
  apply tail_intertwines _ _ _ _ _ fac xReg _ v
  intro w
  change Y *ᵥ (P *ᵥ w) = P *ᵥ (Y' *ᵥ w)
  simp only [Matrix.mulVec_mulVec,eq]
#print axioms actual_tail
end DivisorG3
