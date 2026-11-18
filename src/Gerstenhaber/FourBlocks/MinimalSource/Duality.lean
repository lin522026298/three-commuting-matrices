module

public import Gerstenhaber.FourBlocks.MinimalSource.MinimalCounterexample
public import Gerstenhaber.CanonicalExtension.PositiveDual

/-!
Natural top/socle duality for the actual positive dual action. These are
constructed maps on the literal quotients and annihilators, not abstract
equal-dimension identifications. The first-kernel count is also preserved.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap
open Gerstenhaber.CanonicalExtension

variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

local instance (priority := 50) : Module A (Module.Dual K M) :=
  positiveDualModule (K := K) (A := A) (M := M)
local instance (priority := 50) : IsScalarTower K A (Module.Dual K M) :=
  positiveDual_tower (K := K) (A := A) (M := M)

theorem socle_dual_vanishes_radical (eps : A →ₐ[K] K) (phi : Module.Dual K M)
    (hphi : phi ∈ moduleSocle (M := Module.Dual K M) eps) :
    (moduleRadical (M := M) eps).restrictScalars K ≤ phi.ker := by
  intro x hx
  change phi x=0
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,ha,y,rfl⟩ := hx
    exact LinearMap.congr_fun (hphi a ha) y
  | zero => exact phi.map_zero
  | add x y _ _ hx hy => rw [map_add,hx,hy,add_zero]
  | smul a x _ hx =>
    have h := congrArg (fun psi : Module.Dual K M => psi x)
      (smul_eq_eps_smul_of_mem_socle eps phi hphi a)
    change phi (a • x)=0
    change phi (a • x)=eps a*phi x at h
    rw [h,hx,mul_zero]

theorem dual_socle_eq_annihilator_radical (eps : A →ₐ[K] K) :
    (moduleSocle (M := Module.Dual K M) eps).restrictScalars K =
      ((moduleRadical (M := M) eps).restrictScalars K).dualAnnihilator := by
  ext phi
  constructor
  · intro hphi
    apply (Submodule.mem_dualAnnihilator _).mpr
    exact socle_dual_vanishes_radical eps phi hphi
  · intro hphi a ha
    apply LinearMap.ext
    intro x
    exact (Submodule.mem_dualAnnihilator _).mp hphi _ (smul_mem_moduleRadical eps a ha x)

/-- Pull a functional back from the actual top quotient. -/
def dualTopToSocle (eps : A →ₐ[K] K) :
    Module.Dual K (Top (M := M) eps) →ₗ[K] moduleSocle (M := Module.Dual K M) eps where
  toFun phi := ⟨phi.comp (topProjection eps),by
    intro a ha
    apply LinearMap.ext
    intro x
    change phi (topProjection eps (a • x))=0
    rw [topProjection_smul,ha,zero_smul,map_zero]⟩
  map_add' := by intro phi psi; rfl
  map_smul' := by intro k phi; rfl

@[simp] theorem dualTopToSocle_apply (eps : A →ₐ[K] K)
    (phi : Module.Dual K (Top (M := M) eps)) (x : M) :
    (dualTopToSocle eps phi : Module.Dual K M) x=phi (topProjection eps x) := rfl

theorem dualTopToSocle_bijective (eps : A →ₐ[K] K) :
    Function.Bijective (dualTopToSocle (M := M) eps) := by
  constructor
  · intro phi psi h
    apply LinearMap.ext
    intro q
    obtain ⟨x,rfl⟩ := topProjection_surjective eps q
    exact congrArg (fun f : moduleSocle (M := Module.Dual K M) eps => f.1 x) h
  · intro phi
    let f : (M ⧸ (moduleRadical (M := M) eps).restrictScalars K) →ₗ[K] K :=
      ((moduleRadical eps).restrictScalars K).liftQ phi.1
        (socle_dual_vanishes_radical eps phi.1 phi.2)
    let q : Top (M := M) eps ≃ₗ[K]
        M ⧸ (moduleRadical (M := M) eps).restrictScalars K :=
      (Submodule.Quotient.restrictScalarsEquiv K (moduleRadical eps)).symm
    refine ⟨f.comp q.toLinearMap,?_⟩
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    rfl

def dualTopEquivSocle (eps : A →ₐ[K] K) :
    Module.Dual K (Top (M := M) eps) ≃ₗ[K] moduleSocle (M := Module.Dual K M) eps :=
  LinearEquiv.ofBijective (dualTopToSocle eps) (dualTopToSocle_bijective eps)

theorem dual_radical_coannihilator (eps : A →ₐ[K] K) :
    ((moduleRadical (M := Module.Dual K M) eps).restrictScalars K).dualCoannihilator =
      (moduleSocle (M := M) eps).restrictScalars K := by
  ext x
  constructor
  · intro hx a ha
    apply (Module.forall_dual_apply_eq_zero_iff K (a • x)).mp
    intro phi
    exact (Submodule.mem_dualCoannihilator _).mp hx _ (smul_mem_moduleRadical eps a ha phi)
  · intro hx
    apply (Submodule.mem_dualCoannihilator _).mpr
    intro phi hphi
    induction hphi using Submodule.span_induction with
    | mem phi hphi =>
      obtain ⟨a,ha,psi,rfl⟩ := hphi
      change psi (a • x)=0
      rw [hx a ha,map_zero]
    | zero => rfl
    | add phi psi _ _ hp hq =>
      change phi x+psi x=0
      rw [hp,hq,add_zero]
    | smul a phi _ hp =>
      change phi (a • x)=0
      rw [smul_eq_eps_smul_of_mem_socle eps x hx a,phi.map_smul,hp,smul_zero]

theorem dual_radical_eq_annihilator_socle [FiniteDimensional K M] (eps : A →ₐ[K] K) :
    (moduleRadical (M := Module.Dual K M) eps).restrictScalars K =
      ((moduleSocle (M := M) eps).restrictScalars K).dualAnnihilator := by
  rw [← dual_radical_coannihilator eps]
  exact Subspace.dualCoannihilator_dualAnnihilator_eq.symm

/-- Restriction to the actual socle induces the actual dual top quotient. -/
def topDualEquivSocleDual [FiniteDimensional K M] (eps : A →ₐ[K] K) :
    Top (M := Module.Dual K M) eps ≃ₗ[K] Module.Dual K (moduleSocle (M := M) eps) :=
  (Submodule.Quotient.restrictScalarsEquiv K
    (moduleRadical (M := Module.Dual K M) eps)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (dual_radical_eq_annihilator_socle eps)).trans
      (Subspace.quotAnnihilatorEquiv ((moduleSocle (M := M) eps).restrictScalars K)))

@[simp] theorem topDualEquivSocleDual_mk [FiniteDimensional K M] (eps : A →ₐ[K] K)
    (phi : Module.Dual K M) (x : moduleSocle (M := M) eps) :
    topDualEquivSocleDual eps ((moduleRadical eps).mkQ phi) x=phi x := rfl

theorem dual_socle_finrank [FiniteDimensional K M] (eps : A →ₐ[K] K) :
    finrank K (moduleSocle (M := Module.Dual K M) eps) =
      finrank K (Top (M := M) eps) := by
  rw [← (dualTopEquivSocle eps).finrank_eq,Subspace.dual_finrank_eq]

theorem dual_top_finrank [FiniteDimensional K M] (eps : A →ₐ[K] K) :
    finrank K (Top (M := Module.Dual K M) eps) =
      finrank K (moduleSocle (M := M) eps) := by
  rw [(topDualEquivSocleDual eps).finrank_eq,Subspace.dual_finrank_eq]

theorem dualMap_kernel_finrank [FiniteDimensional K M] (f : Module.End K M) :
    finrank K (LinearMap.ker f.dualMap) = finrank K (LinearMap.ker f) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker f.dualMap
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range,Subspace.dual_finrank_eq] at h2
  omega

theorem positiveDual_first_kernel_finrank [FiniteDimensional K M] (t : A) :
    finrank K (LinearMap.ker (Algebra.lsmul K K (Module.Dual K M) t)) =
      finrank K (LinearMap.ker (Algebra.lsmul K K M t)) :=
  dualMap_kernel_finrank (Algebra.lsmul K K M t)

theorem positiveDual_actionImage_finrank [FiniteDimensional K M] :
    finrank K (actualActionImage (K := K) (A := A) (M := Module.Dual K M)) =
      finrank K (actualActionImage (K := K) (A := A) (M := M)) := by
  rw [actualActionImage_finrank,actualActionImage_finrank,positiveDual_annihilator]

end Gerstenhaber.FourBlocks.MinimalSource
