module

public import PairOrbit
public import Mathlib.LinearAlgebra.Matrix.Reindex

@[expose] public section
noncomputable section
namespace GKGauge
open JordanPrimitive Matrix Module
variable {k F : Type} [Field k] [Infinite k] [Field F] [Algebra k F]
def JordanModels (F : Type) [Field F] : Prop := ∀ (n : ℕ) (U : Matrix (Fin n) (Fin n) F),
    IsNilpotent U → ∃ (d : ℕ) (m : Fin d → ℕ) (e : Ix m ≃ Fin n) (G : Matrix (Ix m) (Ix m) F),
      IsUnit G ∧ (U.submatrix e e)*G=G*matrixJ m ∧
      finrank F (LinearMap.ker (Matrix.toLinAlgEquiv' U)) = ∑ h, m h

theorem nil_matrix_parameters_of_jordan (JM : JordanModels F) (n : ℕ) (Q : Matrix (Fin n) (Fin n) F) (hn : IsNilpotent Q) :
    FieldParams (k:=k) Q (n^2-n) := by
  classical
  obtain ⟨d,m,e,G,hG,hI,hker⟩ := JM n Q hn
  have hcard : Fintype.card (Ix m)=n := (Fintype.card_congr e).trans (Fintype.card_fin n)
  have hd := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det G).mp hG)
  have hp := single_given_shape (k:=k) m _ ⟨G,hd,hI⟩
  rw [hcard] at hp
  obtain ⟨w,hw⟩ := hp
  refine ⟨w,?_⟩
  intro L h i j
  have hh := hw L h (e.symm i) (e.symm j)
  simpa [Matrix.submatrix_apply] using hh

/-- Conditional only on the stated Jordan-normal-basis theorem; no scalar parameter or dimension premise. -/
theorem subregular_pair_parameters_of_jordan (JM : JordanModels F) {n : ℕ} (U V : Matrix (Fin n) (Fin n) F)
    (h : Commute U V) (hn : IsNilpotent U) (hz : IsNilpotent V)
    (hk : 2 ≤ finrank F U.mulVecLin.ker) :
    ∃ s : Finset F, s.card ≤ n*n-2 ∧
      (∀ i j, U i j ∈ IntermediateField.adjoin k (s : Set F)) ∧
      (∀ i j, V i j ∈ IntermediateField.adjoin k (s : Set F)) := by
  classical
  obtain ⟨d,m,e,G,hG,hI,hker⟩ := JM n U hn
  let f := Matrix.reindexAlgEquiv F F e.symm
  have hu (M : Matrix _ _ F) : f M = M.submatrix e e := rfl
  have hC := h.map f.toAlgHom
  have hN := hz.map f.toAlgHom
  change Commute (f U) (f V) at hC
  change IsNilpotent (f V) at hN
  rw [hu,hu] at hC
  rw [hu] at hN
  obtain ⟨s,hs,hU,hV⟩ := pair_given_shape (k:=k) m (nil_matrix_parameters_of_jordan (k:=k) JM) _ _ hC hN
    ⟨G,isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det G).mp hG),hI⟩
  have hcard : Fintype.card (Ix m)=n := (Fintype.card_congr e).trans (Fintype.card_fin n)
  rw [hcard,pow_two] at hs
  change 2 ≤ finrank F (Matrix.toLinAlgEquiv' U).ker at hk
  rw [hker] at hk
  refine ⟨s,hs.trans (Nat.sub_le_sub_left hk _),?_,?_⟩
  · intro i j; simpa [Matrix.submatrix_apply] using hU (e.symm i) (e.symm j)
  · intro i j; simpa [Matrix.submatrix_apply] using hV (e.symm i) (e.symm j)
end GKGauge
#print axioms GKGauge.nil_matrix_parameters_of_jordan
#print axioms GKGauge.subregular_pair_parameters_of_jordan
