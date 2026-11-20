module

public import AnyMinors
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section
noncomputable section
namespace DivisorG3
open Module IsDiscreteValuationRing
variable {V ι κ : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
abbrev colQuot (A : Matrix ι κ V) := (ι → V) ⧸ matrixColumnLattice A
theorem valuation_prod {α : Type*} (s : Finset α) (f : α → V) :
    addVal V (∏ i ∈ s, f i) = ∑ i ∈ s, addVal V (f i) := by
  classical induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ hx ih => simp [hx,ih]

/-- Entirely internal to the DVR V: no residue-field section, coefficient field,
completion, formal parameter or rational base point is an input. -/
theorem intrinsic_smith (A : Matrix ι κ V) (s : ι → κ) (hs : (A.submatrix id s).det≠0) :
    ∃ g : V, g≠0 ∧ allColumnMinorIdeal A = Ideal.span ({g}:Set _) ∧
      length V (colQuot A) = addVal V g := by
  let b := Pi.basisFun V ι
  let N := matrixColumnLattice A
  have h : finrank V N = finrank V (ι→V) := by
    rw [Module.finrank_pi]
    change A.rank = Fintype.card ι
    exact le_antisymm A.rank_le_card_height (Matrix.rank_of_det_ne_zero hs ▸ A.rank_submatrix_le id s)
  let a := Submodule.smithNormalFormCoeffs b h
  have ha (i) : a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h i
  refine ⟨∏ i,a i,Finset.prod_ne_zero_iff.mpr (fun i _ => ha i),?_,?_⟩
  · rw [←latticeVolumeIdeal_matrixColumnLattice,latticeVolumeIdeal_eq_span_smith b _ h]
  · rw [(N.quotientEquivPiSpan b h).length_eq,Module.length_pi_of_fintype,valuation_prod]
    exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (a i)
theorem intrinsic_colength (A : Matrix ι κ V) (s : ι → κ) (hs : (A.submatrix id s).det≠0) :
    length V (V ⧸ allColumnMinorIdeal A) = length V (colQuot A) ∧ IsFiniteLength V (colQuot A) := by
  obtain ⟨g,hg,he,hl⟩ := intrinsic_smith A s hs
  refine ⟨?_,Module.length_ne_top_iff.mp (hl ▸ addVal_eq_top_iff.not.mpr hg)⟩
  rw [he,hl]
  exact Ring.ord_eq_addVal g

/-- Strict index inequality iff an actual minor beats the given element, on any DVR. -/
theorem intrinsic_witness (A : Matrix ι κ V) (s : ι → κ) (hs : (A.submatrix id s).det≠0) (c : V) :
    length V (colQuot A) < addVal V c ↔ ∃ j : ι → κ, addVal V (A.submatrix id j).det < addVal V c := by
  obtain ⟨g,_,he,hl⟩ := intrinsic_smith A s hs
  rw [hl]
  constructor
  · intro hn
    by_contra! h
    have le : allColumnMinorIdeal A ≤ Ideal.span ({c}:Set V) :=
      Ideal.span_le.mpr fun _ ⟨j,ej⟩ => ej ▸ Ideal.mem_span_singleton.mpr (addVal_le_iff_dvd.mp (h j))
    exact (not_le_of_gt hn) (addVal_le_iff_dvd.mpr (Ideal.mem_span_singleton.mp
      (le (he ▸ Ideal.subset_span (Set.mem_singleton g)))))
  · rintro ⟨j,hj⟩
    apply lt_of_le_of_lt _ hj
    apply addVal_le_iff_dvd.mpr
    apply Ideal.mem_span_singleton.mp
    rw [←he]
    exact Ideal.subset_span ⟨j,rfl⟩

omit [IsDomain V] [IsDiscreteValuationRing V] in
theorem square_minor_ideal (P : Matrix ι ι V) : allColumnMinorIdeal P = Ideal.span ({P.det}:Set V) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨s,rfl⟩
    apply Ideal.mem_span_singleton.mpr
    let E := (1 : Matrix ι ι V).submatrix id s
    have he : P.submatrix id s = P * E := by ext i j; simp [E,Matrix.mul_apply,Matrix.one_apply]
    exact ⟨E.det,(congrArg Matrix.det he).trans (Matrix.det_mul P E)⟩
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply Ideal.subset_span
    exact ⟨id,rfl⟩

theorem intrinsic_square (P : Matrix ι ι V) (hp : P.det≠0) :
    length V (colQuot P) = addVal V P.det := by
  obtain ⟨h,_⟩ := intrinsic_colength P id (by exact hp)
  rw [←h,square_minor_ideal]
  exact Ring.ord_eq_addVal _
#print axioms intrinsic_colength
#print axioms intrinsic_witness
#print axioms intrinsic_square
end DivisorG3
