module

public import Gerstenhaber.FourBlocks.MinimalSource.Pencil
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
The number of nilpotent t-blocks is the dimension of ker t.  The two
intertwining lemmas prove its required monotonicity on actual invariant
submodules and quotients, without a Jordan-form classification.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem finrank_ker_eq_quotient_range [FiniteDimensional K V] (f : Module.End K V) :
    finrank K (LinearMap.ker f) = finrank K (V ⧸ LinearMap.range f) := by
  have hker := f.finrank_range_add_finrank_ker
  have hquot := (LinearMap.range f).finrank_quotient_add_finrank
  omega

def intertwiningKernelMap (f : Module.End K V) (g : Module.End K W)
    (i : V →ₗ[K] W) (hi : ∀ x, i (f x)=g (i x)) :
    LinearMap.ker f →ₗ[K] LinearMap.ker g where
  toFun x := ⟨i x,by
    change g (i x)=0
    rw [← hi,x.2,map_zero]⟩
  map_add' x y := Subtype.ext (i.map_add x y)
  map_smul' a x := Subtype.ext (i.map_smul a x)

theorem finrank_ker_le_of_injective_intertwining [FiniteDimensional K W]
    (f : Module.End K V) (g : Module.End K W) (i : V →ₗ[K] W)
    (hi : Function.Injective i) (hcomm : ∀ x, i (f x)=g (i x)) :
    finrank K (LinearMap.ker f) ≤ finrank K (LinearMap.ker g) := by
  apply LinearMap.finrank_le_finrank_of_injective
    (f := intertwiningKernelMap f g i hcomm)
  intro x y hxy
  apply Subtype.ext
  exact hi (congrArg (fun z : LinearMap.ker g => (z : W)) hxy)

def intertwiningCokernelMap (f : Module.End K V) (g : Module.End K W)
    (p : V →ₗ[K] W) (hcomm : ∀ x, p (f x)=g (p x)) :
    (V ⧸ LinearMap.range f) →ₗ[K] (W ⧸ LinearMap.range g) :=
  (LinearMap.range f).liftQ ((LinearMap.range g).mkQ.comp p) (by
    rintro _ ⟨x,rfl⟩
    change (LinearMap.range g).mkQ (p (f x))=0
    rw [hcomm]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨p x,rfl⟩)

theorem intertwiningCokernelMap_surjective
    (f : Module.End K V) (g : Module.End K W) (p : V →ₗ[K] W)
    (hp : Function.Surjective p) (hcomm : ∀ x, p (f x)=g (p x)) :
    Function.Surjective (intertwiningCokernelMap f g p hcomm) := by
  intro y
  obtain ⟨w,rfl⟩ := (LinearMap.range g).mkQ_surjective y
  obtain ⟨x,rfl⟩ := hp w
  exact ⟨(LinearMap.range f).mkQ x,rfl⟩

theorem finrank_ker_le_of_surjective_intertwining
    [FiniteDimensional K V] [FiniteDimensional K W]
    (f : Module.End K V) (g : Module.End K W) (p : V →ₗ[K] W)
    (hp : Function.Surjective p) (hcomm : ∀ x, p (f x)=g (p x)) :
    finrank K (LinearMap.ker g) ≤ finrank K (LinearMap.ker f) := by
  rw [finrank_ker_eq_quotient_range,finrank_ker_eq_quotient_range]
  exact LinearMap.finrank_le_finrank_of_surjective
    (intertwiningCokernelMap_surjective f g p hp hcomm)

end Gerstenhaber.FourBlocks.MinimalSource
