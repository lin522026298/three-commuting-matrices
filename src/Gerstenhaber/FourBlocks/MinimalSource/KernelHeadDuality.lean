module

public import Gerstenhaber.FourBlocks.MinimalSource.Duality
public import Gerstenhaber.FourBlocks.HeadBounds.HeadModule

/-!
The natural positive-dual identification of the actual first kernel
with the dual of the actual dual head. Evaluation and quotient lifts
provide the maps; equal dimensions are not used as a module isomorphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap
open Gerstenhaber.CanonicalExtension
open Gerstenhaber.FourBlocks.HeadBounds

variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

local instance (priority := 50) : Module A (Module.Dual K M) :=
  positiveDualModule (K := K) (A := A) (M := M)
local instance (priority := 50) : IsScalarTower K A (Module.Dual K M) :=
  positiveDual_tower (K := K) (A := A) (M := M)
local instance (priority := 50) : Module A (Module.Dual K (Module.Dual K M)) :=
  positiveDualModule (K := K) (A := A) (M := Module.Dual K M)
local instance (priority := 50) : IsScalarTower K A (Module.Dual K (Module.Dual K M)) :=
  positiveDual_tower (K := K) (A := A) (M := Module.Dual K M)

def positiveBidualEvaluation : M →ₗ[A] Module.Dual K (Module.Dual K M) where
  toFun := Module.Dual.eval K M
  map_add' := (Module.Dual.eval K M).map_add
  map_smul' := by intro a x; ext phi; rfl

@[simp] theorem positiveBidualEvaluation_apply (x : M) (phi : Module.Dual K M) :
    positiveBidualEvaluation (A := A) x phi=phi x := rfl

def positiveBidualEquiv [FiniteDimensional K M] :
    M ≃ₗ[A] Module.Dual K (Module.Dual K M) :=
  LinearEquiv.ofBijective positiveBidualEvaluation (Module.bijective_dual_eval K M)

def tKernel (t : A) : Submodule A M := (t • (LinearMap.id : M →ₗ[A] M)).ker

@[simp] theorem mem_tKernel (t : A) (x : M) : x ∈ tKernel t ↔ t • x=0 := Iff.rfl

local instance (priority := 50) (t : A) :
    Module A (Module.Dual K (ActualHead (M := Module.Dual K M) t)) :=
  positiveDualModule (K := K) (A := A) (M := ActualHead (M := Module.Dual K M) t)
local instance (priority := 50) (t : A) :
    IsScalarTower K A (Module.Dual K (ActualHead (M := Module.Dual K M) t)) :=
  positiveDual_tower (K := K) (A := A) (M := ActualHead (M := Module.Dual K M) t)

def kernelHeadFunctional (t : A) (x : tKernel (M := M) t) :
    Module.Dual K (ActualHead (M := Module.Dual K M) t) :=
  let f := ((tImage (M := Module.Dual K M) t).restrictScalars K).liftQ
    (Module.Dual.eval K M x.1) (by
      rintro _ ⟨phi,rfl⟩
      change phi (t • x.1)=0
      have hx : t • x.1=0 := x.2
      rw [hx,map_zero])
  f.comp (Submodule.Quotient.restrictScalarsEquiv K (tImage (M := Module.Dual K M) t)).symm.toLinearMap

@[simp] theorem kernelHeadFunctional_mk (t : A) (x : tKernel (M := M) t)
    (phi : Module.Dual K M) :
    kernelHeadFunctional t x (headProjection t phi)=phi x.1 := rfl

def kernelToDualHead (t : A) :
    tKernel (M := M) t →ₗ[A] Module.Dual K (ActualHead (M := Module.Dual K M) t) where
  toFun := kernelHeadFunctional t
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro q
    obtain ⟨phi,rfl⟩ := headProjection_surjective (M := Module.Dual K M) t q
    exact phi.map_add x.1 y.1
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro q
    obtain ⟨phi,rfl⟩ := headProjection_surjective (M := Module.Dual K M) t q
    rfl

theorem kernelToDualHead_bijective [FiniteDimensional K M] (t : A) :
    Function.Bijective (kernelToDualHead (K := K) (M := M) t) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (Module.bijective_dual_eval K M).1
    apply LinearMap.ext
    intro phi
    exact congrArg (fun f => f (headProjection t phi)) hxy
  · intro f
    let g : Module.Dual K (Module.Dual K M) :=
      f.comp ((headProjection (M := Module.Dual K M) t).restrictScalars K)
    let x : M := (Module.evalEquiv K M).symm g
    have hx : t • x=0 := by
      apply (Module.forall_dual_apply_eq_zero_iff K (t • x)).mp
      intro phi
      change (t • phi) x=0
      rw [Module.apply_evalEquiv_symm_apply]
      change f (headProjection t (t • phi))=0
      rw [(headProjection t).map_smul,head_t_zero,map_zero]
    refine ⟨⟨x,hx⟩,?_⟩
    apply LinearMap.ext
    intro q
    obtain ⟨phi,rfl⟩ := headProjection_surjective (M := Module.Dual K M) t q
    change phi ((Module.evalEquiv K M).symm g)=f (headProjection t phi)
    exact Module.apply_evalEquiv_symm_apply K M phi g

def kernelDualHeadEquiv [FiniteDimensional K M] (t : A) :
    tKernel (M := M) t ≃ₗ[A] Module.Dual K (ActualHead (M := Module.Dual K M) t) :=
  LinearEquiv.ofBijective (kernelToDualHead t) (kernelToDualHead_bijective t)

@[simp] theorem kernelDualHeadEquiv_mk [FiniteDimensional K M] (t : A)
    (x : tKernel (M := M) t) (phi : Module.Dual K M) :
    kernelDualHeadEquiv t x (headProjection t phi)=phi x.1 := rfl

end Gerstenhaber.FourBlocks.MinimalSource
