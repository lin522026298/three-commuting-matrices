module

public import ActualMinimalEnds
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section
noncomputable section
namespace GKEnds
open Module LinearMap
open Gerstenhaber.FourBlocks.MinimalSource
variable {k ι M A : Type*} [Field k] [Fintype ι] [DecidableEq ι]
variable [CommRing A] [Algebra k A] [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

structure SubregularPair (U V : Matrix ι ι k) : Prop where
  comm : Commute U V
  nilY : IsNilpotent U
  nilZ : IsNilpotent V
  width : 2 ≤ finrank k U.mulVecLin.ker

theorem coordinate_criterion (e : (ι → k) ≃ₗ[k] M) (U V : Matrix ι ι k) (y z : A)
    (hy : IsNilpotent y) (hz : IsNilpotent z)
    (ey : ∀ v, e (U.mulVecLin v)=y • e v) (ez : ∀ v, e (V.mulVecLin v)=z • e v)
    (wide : 2 ≤ finrank k (Algebra.lsmul k k M y).ker) : SubregularPair U V := by
  let g : Matrix ι ι k ≃ₐ[k] End k M := Matrix.toLinAlgEquiv'.trans (e.conjAlgEquiv k)
  have rec_ (D : Matrix ι ι k) (a : A) (h : ∀v,e (D.mulVecLin v)=a • e v) :
      g D=Algebra.lsmul k k M a := by
    ext w
    obtain ⟨v,rfl⟩ := e.surjective w
    change e (D.mulVecLin (e.symm (e v))) = a • e v
    rw [e.symm_apply_apply]; exact h v
  have fy := rec_ U y ey
  have fz := rec_ V z ez
  refine ⟨Commute.of_map g.injective ?_,(IsNilpotent.map_iff g.injective).mp ?_,
    (IsNilpotent.map_iff g.injective).mp ?_,wide.trans ?_⟩
  · rw [fy,fz]; exact (Commute.all y z).map (Algebra.lsmul k k M)
  · rw [fy]; exact hy.map (Algebra.lsmul k k M)
  · rw [fz]; exact hz.map (Algebra.lsmul k k M)
  · apply finrank_ker_le_of_injective_intertwining _ _ e.symm.toLinearMap e.symm.injective
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    change e.symm (y • e v)=U.mulVecLin (e.symm (e v))
    rw [←ey,e.symm_apply_apply,e.symm_apply_apply]
end GKEnds
