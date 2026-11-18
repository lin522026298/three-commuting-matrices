import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
open scoped TensorProduct
namespace G3Scalar
open Module
variable (k : Type*) (L : Type*) [Field k] [Field L] [Algebra k L]
variable {n : ℕ}
abbrev extendMatrix : Matrix (Fin n) (Fin n) k →ₐ[k] Matrix (Fin n) (Fin n) L :=
  (Algebra.ofId k L).mapMatrix

variable (A : Subalgebra k (Matrix (Fin n) (Fin n) k))

/-- The natural L-linear algebra map for the actual subalgebra of matrices:
on simple tensors it applies entrywise inclusion and left scalar multiplication. -/
def tensorActor : L ⊗[k] A →ₐ[L] Matrix (Fin n) (Fin n) L :=
  AlgHom.liftEquiv k L _ _ ((extendMatrix k L).comp A.val)

@[simp] theorem tensorActor_tmul (a : L) (M : A) :
    tensorActor k L A (a ⊗ₜ[k] M) = a • extendMatrix k L M := rfl

theorem tensorActor_injective : Function.Injective (tensorActor k L A) := by
  let f := A.val.toLinearMap.lTensor L
  have h (z : L ⊗[k] A) :
      tensorActor k L A z = (matrixEquivTensor (Fin n) k L).symm (f z) := by
    induction z with
    | tmul a m => rfl
    | add a b ha hb => simpa only [map_add] using congrArg₂ (·+·) ha hb
  intro x y hxy
  rw [h,h] at hxy
  exact Module.Flat.lTensor_preserves_injective_linearMap A.val.toLinearMap Subtype.val_injective
    ((matrixEquivTensor (Fin n) k L).symm.injective hxy)

variable (S : Set (Matrix (Fin n) (Fin n) k))

theorem tensorActor_range :
    (tensorActor k L (Algebra.adjoin k S)).range =
      Algebra.adjoin L (extendMatrix k L '' S) := by
  let B := Algebra.adjoin L (extendMatrix k L '' S)
  have hA : Algebra.adjoin k S ≤ (B.restrictScalars k).comap (extendMatrix k L) := by
    apply Algebra.adjoin_le
    intro x hx
    exact Algebra.subset_adjoin ⟨x,hx,rfl⟩
  apply le_antisymm
  · rintro x ⟨z,rfl⟩
    induction z with
    | tmul a m => exact B.smul_mem (hA m.property) a
    | add x y hx hy => rw [map_add]; exact B.add_mem hx hy
  · apply Algebra.adjoin_le
    rintro _ ⟨s,hs,rfl⟩
    exact ⟨1 ⊗ₜ[k] ⟨s, Algebra.subset_adjoin hs⟩, by simp⟩

/-- The natural algebra isomorphism for the original generated matrix algebra. -/
def adjoinTensorEquiv :
    L ⊗[k] (Algebra.adjoin k S) ≃ₐ[L] Algebra.adjoin L (extendMatrix k L '' S) :=
  (AlgEquiv.ofInjective (tensorActor k L _) (tensorActor_injective k L _)).trans
    (Subalgebra.equivOfEq _ _ (tensorActor_range k L S))

@[simp] theorem adjoinTensorEquiv_tmul (a : L) (s : Algebra.adjoin k S) :
    (adjoinTensorEquiv k L S (a ⊗ₜ[k] s) : Matrix (Fin n) (Fin n) L) =
      a • extendMatrix k L s := rfl

/-- Literal equality of dimensions after arbitrary scalar extension; S need not
be a commuting family and the fields may lie in different universes. -/
theorem finrank_adjoin_map :
    finrank k (Algebra.adjoin k S) = finrank L (Algebra.adjoin L (extendMatrix k L '' S)) := by
  rw [← Module.finrank_baseChange (R := L) (S := k)]
  exact (adjoinTensorEquiv k L S).toLinearEquiv.finrank_eq

#print axioms tensorActor_injective
#print axioms tensorActor_range
#print axioms adjoinTensorEquiv
#print axioms adjoinTensorEquiv_tmul
#print axioms finrank_adjoin_map
end G3Scalar
