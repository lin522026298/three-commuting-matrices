import DVRScalar
import AnyMinors
import Mathlib.LinearAlgebra.Matrix.Rank
noncomputable section
namespace DivisorG3
open Module PowerSeries
variable {k ι κ : Type*} [Field k] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
abbrev matQuot (A : Matrix ι κ (O k)) := (ι → O k) ⧸ matrixColumnLattice A
omit [DecidableEq κ] in
theorem full_of_minor (A : Matrix ι κ (O k)) (s : ι → κ) (hs : (A.submatrix id s).det≠0) :
    finrank (O k) (matrixColumnLattice A) = finrank (O k) (ι → O k) := by
  rw [Module.finrank_pi]
  change A.rank = Fintype.card ι
  exact le_antisymm A.rank_le_card_height (Matrix.rank_of_det_ne_zero hs ▸ A.rank_submatrix_le id s)

theorem smith_colength (A : Matrix ι κ (O k)) (s : ι → κ) (hs : (A.submatrix id s).det≠0) :
    ∃ g : O k, g≠0 ∧ allColumnMinorIdeal A = Ideal.span ({g}:Set _) ∧
      finrank k (matQuot A) = g.order.toNat ∧ Module.Finite k (matQuot A) := by
  let b := Pi.basisFun (O k) ι
  let N := matrixColumnLattice A
  have h := full_of_minor A s hs
  let a := Submodule.smithNormalFormCoeffs b h
  have ha (i) : a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h i
  let (i : ι) : FiniteDimensional k (O k ⧸ Ideal.span ({a i}:Set _)) := principal_finite _ (ha i)
  refine ⟨∏ i,a i,Finset.prod_ne_zero_iff.mpr (fun i _ => ha i),?_,?_,?_⟩
  · rw [←latticeVolumeIdeal_matrixColumnLattice, latticeVolumeIdeal_eq_span_smith b _ h]
  · change finrank k ((ι→O k) ⧸ N) = _
    rw [N.finrank_quotient_eq_sum k b h,order_prod,ENat.toNat_sum (fun i _ => order_eq_top.not.mpr (ha i))]
    exact Finset.sum_congr rfl fun i _ => principal_length _ (ha i)
  · let e := (N.quotientEquivPiSpan b h).restrictScalars k
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

theorem minor_length (A : Matrix ι κ (O k)) (s : ι → κ) (hs : (A.submatrix id s).det≠0) :
    finrank k (O k ⧸ allColumnMinorIdeal A) = finrank k (matQuot A) := by
  obtain ⟨g,hg,he,hq,_⟩ := smith_colength A s hs
  rw [he,hq,principal_length _ hg]

/-- The length threshold really witnesses an individual maximal minor of the supplied
rectangular matrix; no arc-witness or determinantal inequality is assumed. -/
theorem bad_minor (A : Matrix ι κ (O k)) (s : ι → κ) (hs : (A.submatrix id s).det≠0)
    (q : ℕ) (hq : finrank k (matQuot A)<q) : ∃ j : ι → κ, (A.submatrix id j).det.order < q := by
  obtain ⟨g,hg,he,hqg,_⟩ := smith_colength A s hs
  by_contra! hn
  have contain : allColumnMinorIdeal A ≤ Ideal.span ({(PowerSeries.X : O k)^q}:Set _) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Ideal.mem_span_singleton.mpr (X_pow_dvd_iff.mpr (nat_le_order_iff.mp (hn j)))
  have hg' : g ∈ allColumnMinorIdeal A := he ▸ Ideal.subset_span (Set.mem_singleton g)
  have hge : (q : ℕ∞) ≤ g.order := nat_le_order_iff.mpr (X_pow_dvd_iff.mp (Ideal.mem_span_singleton.mp (contain hg')))
  rw [←coe_toNat_order hg,ENat.natCast_le_natCast,←hqg] at hge
  exact (not_lt_of_ge hge) hq

#print axioms smith_colength
#print axioms minor_length
#print axioms bad_minor
end DivisorG3
