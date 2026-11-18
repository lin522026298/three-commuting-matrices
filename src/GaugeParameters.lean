import MatrixGauge
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
namespace GKGauge
open Module Matrix Finset
universe u
variable {F k : Type u} [Field k] [Infinite k] [Field F] [Algebra k F]
variable {n : Type u} [Fintype n] [DecidableEq n]

theorem gauge_parameters (S : Submodule F (Matrix n n F)) (h : ∃ z : S, z.val.det ≠ 0) :
    ∃ z : S, z.val.det ≠ 0 ∧ ∃ s : Finset F,
      s.card ≤ Fintype.card n * Fintype.card n - finrank F S ∧
      ∀ i j, z.val i j ∈ IntermediateField.adjoin k (s : Set F) := by
  classical
  obtain ⟨z,hz,a,ha⟩ := gauge_subspace (k:=k) S h
  let p : Finset (n × n) := univ.map a
  let g : n × n → F := fun t => z.val t.1 t.2
  let s := pᶜ.image g
  refine ⟨z,hz,s, ?_, ?_⟩
  · calc
      s.card ≤ pᶜ.card := card_image_le
      _ = _ := by rw [Finset.card_compl]; simp [p]
  · intro i j
    by_cases hi : (i,j) ∈ p
    · obtain ⟨l,_,hl⟩ := mem_map.mp hi
      have e := ha l; rw [hl] at e
      obtain ⟨v,hv⟩ := e
      rw [← hv]; exact IntermediateField.algebraMap_mem _ _
    · exact IntermediateField.subset_adjoin k _ (mem_image.mpr ⟨(i,j),mem_compl.mpr hi,rfl⟩)

omit [Infinite k] in
/-- Integrality of matrix recovery over the *field* of the parameters:
A H = H J and H invertible suffice. -/
theorem recovery_mem (L : IntermediateField k F) (A H J : Matrix n n F)
    (hH : ∀ i j, H i j ∈ L) (hJ : ∀ i j, J i j ∈ L)
    (hdet : H.det ≠ 0) (hi : A * H = H * J) : ∀ i j, A i j ∈ L := by
  let H' : Matrix n n L := fun i j => ⟨_, hH i j⟩
  let J' : Matrix n n L := fun i j => ⟨_, hJ i j⟩
  let f : L →+* F := L.val.toRingHom
  have hf : f.mapMatrix H' = H := rfl
  have hj : f.mapMatrix J' = J := rfl
  have hd : H'.det ≠ 0 := by
    intro h; apply hdet
    rw [← hf, ← RingHom.map_det, h, map_zero]
  have hone : H * f.mapMatrix (H'⁻¹) = 1 := by
    rw [← hf, ← map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd), map_one]
  have he : f.mapMatrix (H' * J' * H'⁻¹) = A := by
    rw [map_mul,map_mul,hf,hj,← hi, Matrix.mul_assoc, hone, Matrix.mul_one]
  intro i j
  rw [← he]
  exact ((H' * J' * H'⁻¹) i j).property

end GKGauge
#print axioms GKGauge.gauge_parameters
#print axioms GKGauge.recovery_mem
