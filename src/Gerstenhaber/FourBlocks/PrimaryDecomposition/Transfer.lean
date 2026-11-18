module

public import Gerstenhaber.FourBlocks.PrimaryDecomposition.JointSpaces
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-! Transfer from the explicitly quantified nilpotent first-kernel
bound to arbitrary commuting triples over an algebraically closed
field. This file proves an implication; it does not assert its open
nilpotent input. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

universe u

namespace Gerstenhaber.FourBlocks.PrimaryDecomposition

open Module LinearMap

/-- Precisely the nilpotent triple bound, with no generalized G3 input.
All carrier types lie in the same universe as the field. -/
def NilTripleKernelBound (K : Type u) [Field K] (k : ℕ) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : Fin 3 → Module.End K V),
    (∀ i j, Commute (T i) (T j)) → (∀ i, IsNilpotent (T i)) →
    finrank K (T 0).ker ≤ k →
      finrank K (Algebra.adjoin K (Set.range T)) ≤ finrank K V

variable {K V : Type u} [Field K] [IsAlgClosed K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem commuting_triple_bound_of_nilpotent_bound (k : ℕ)
    (hnil : NilTripleKernelBound K k) (T : Fin 3 → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hfirst : ∀ lambda : K, finrank K (T 0-lambda • 1).ker ≤ k) :
    finrank K (Algebra.adjoin K (Set.range T)) ≤ finrank K V := by
  let := jointCharactersFintype T hcomm
  have hlocal (chi : JointCharacters T) :
      finrank K (Generated (restricted T (jointSpace T chi.val)
        (jointSpace_stable T hcomm chi.val))) ≤ finrank K (jointSpace T chi.val) := by
    have h := hnil (jointSpace T chi.val)
      (shifted (restricted T (jointSpace T chi.val) (jointSpace_stable T hcomm chi.val)) chi.val)
      (shifted_commute _ chi.val (restricted_commute T _ _ hcomm))
      (joint_shift_nilpotent T hcomm chi.val)
      ((joint_shift_kernel_le T hcomm chi.val 0).trans (hfirst (chi.val 0)))
    change finrank K (Generated (shifted (restricted T (jointSpace T chi.val)
      (jointSpace_stable T hcomm chi.val)) chi.val)) ≤ _ at h
    rw [adjoin_shifted] at h
    exact h
  have h := generated_finrank_le_sum T
    (fun chi : JointCharacters T => jointSpace T chi.val)
    (fun chi => jointSpace_stable T hcomm chi.val) (jointCharacters_iSup T hcomm) hlocal
  rw [sum_finrank_jointSpace T hcomm] at h
  exact h

theorem matrix_triple_bound_of_nilpotent_bound (k : ℕ)
    (hnil : NilTripleKernelBound K k) (n : ℕ)
    (T : Fin 3 → Matrix (Fin n) (Fin n) K)
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hfirst : ∀ lambda : K,
      finrank K (Matrix.toLin' (T 0-lambda • 1)).ker ≤ k) :
    finrank K (Algebra.adjoin K (Set.range T)) ≤ n := by
  let e : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K) := Matrix.toLinAlgEquiv'
  let U : Fin 3 → Module.End K (Fin n → K) := fun i => e (T i)
  have hUcomm : ∀ i j, Commute (U i) (U j) := fun i j => (hcomm i j).map e.toAlgHom
  have hUfirst : ∀ lambda : K, finrank K (U 0-lambda • 1).ker ≤ k := by
    intro lambda
    have h := hfirst lambda
    have heq : U 0-lambda • 1=e (T 0-lambda • 1) := by simp [U]
    rw [heq]
    exact h
  have hbound := commuting_triple_bound_of_nilpotent_bound k hnil U hUcomm hUfirst
  have hmap : Generated U=(Algebra.adjoin K (Set.range T)).map e.toAlgHom := by
    rw [AlgHom.map_adjoin,←Set.range_comp]
    rfl
  have hdim : finrank K ((Algebra.adjoin K (Set.range T)).map e.toAlgHom)=
      finrank K (Algebra.adjoin K (Set.range T)) :=
    e.toLinearEquiv.finrank_map_eq (Algebra.adjoin K (Set.range T)).toSubmodule
  change finrank K (Generated U) ≤ _ at hbound
  rw [hmap,hdim] at hbound
  simpa using hbound

end Gerstenhaber.FourBlocks.PrimaryDecomposition
