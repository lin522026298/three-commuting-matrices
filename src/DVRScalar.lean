import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.ENat.BigOperators
noncomputable section
namespace DivisorG3
open PowerSeries Module LinearMap
variable {k : Type*} [Field k]
abbrev O (k : Type*) := PowerSeries k
def firstCoeffs (k : Type*) [Field k] (n : ℕ) : O k →ₗ[k] Fin n → k :=
  LinearMap.pi fun i => PowerSeries.coeff i.val
theorem firstCoeffs_surj (n : ℕ) : Function.Surjective (firstCoeffs k n) := by
  intro c
  refine ⟨PowerSeries.mk fun j => if h : j<n then c ⟨j,h⟩ else 0,?_⟩
  funext i
  simp [firstCoeffs,i.isLt]
theorem firstCoeffs_ker (n : ℕ) :
    (firstCoeffs k n).ker = (Ideal.span ({(PowerSeries.X : O k)^n} : Set _)).restrictScalars k := by
  ext f
  change (fun i : Fin n => coeff i.val f) = 0 ↔ f ∈ Ideal.span _
  rw [Ideal.mem_span_singleton,X_pow_dvd_iff]
  constructor
  · intro h j hj; exact congrFun h ⟨j,hj⟩
  · intro h; funext i; exact h i.val i.isLt

def principalJetEquiv (f : O k) (h : f ≠ 0) :
    (O k ⧸ Ideal.span ({f} : Set _)) ≃ₗ[k] (Fin f.order.toNat → k) := by
  have he : Ideal.span ({f} : Set _) = Ideal.span ({(PowerSeries.X : O k)^f.order.toNat} : Set _) := by
    conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f:=f)]
    exact Ideal.span_singleton_mul_right_unit (isUnit_divided_by_X_pow_order h) _
  let e := (firstCoeffs k f.order.toNat).quotKerEquivOfSurjective (firstCoeffs_surj _)
  exact (Submodule.Quotient.restrictScalarsEquiv k _).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (he ▸ (firstCoeffs_ker _).symm) ≪≫ₗ e

theorem principal_length (f : O k) (h : f≠0) :
    finrank k (O k ⧸ Ideal.span ({f} : Set _)) = f.order.toNat := by
  rw [(principalJetEquiv f h).finrank_eq,Module.finrank_pi,Fintype.card_fin]

theorem principal_finite (f : O k) (h : f≠0) :
    Module.Finite k (O k ⧸ Ideal.span ({f} : Set _)) :=
  Module.Finite.of_surjective (principalJetEquiv f h).symm.toLinearMap (principalJetEquiv f h).symm.surjective
#print axioms principal_length
#print axioms principal_finite
end DivisorG3
