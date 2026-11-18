module

public import Gerstenhaber.FourBlocks.MinimalSource.MaximalCyclic

/-!
The cyclic parent is the actual algebra quotient A/Ann(Au), with its
actual A-linear identification with Au. Its descended augmentation and
natural socle map prove the parent's socle dimension without an abstract
length identification or a canonical-module assumption.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap

variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

def cyclicGeneratorMap (u : M) : A →ₗ[A] cyclicModule (A := A) u where
  toFun a := ⟨a • u,Submodule.mem_span_singleton.mpr ⟨a,rfl⟩⟩
  map_add' := by intro a b; apply Subtype.ext; exact add_smul a b u
  map_smul' := by intro a b; apply Subtype.ext; exact mul_smul a b u

theorem cyclicGeneratorMap_surjective (u : M) :
    Function.Surjective (cyclicGeneratorMap (A := A) u) := by
  intro x
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp x.2
  exact ⟨a,Subtype.ext ha⟩

theorem cyclicGeneratorMap_kernel (u : M) :
    (cyclicGeneratorMap (A := A) u).ker = Module.annihilator A (cyclicModule (A := A) u) := by
  ext a
  constructor
  · intro ha
    have hau : a • u=0 := congrArg Subtype.val ha
    apply (mem_annihilator_submodule_iff (cyclicModule (A := A) u) a).mpr
    intro x hx
    obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [← mul_smul,mul_comm a b,mul_smul,hau,smul_zero]
  · intro ha
    apply Subtype.ext
    exact (mem_annihilator_submodule_iff (cyclicModule (A := A) u) a).mp ha u
      (Submodule.mem_span_singleton_self u)

abbrev CyclicParent (u : M) := A ⧸ Module.annihilator A (cyclicModule (A := A) u)

def cyclicParentEquiv (u : M) : CyclicParent (A := A) u ≃ₗ[A] cyclicModule (A := A) u :=
  (Submodule.quotEquivOfEq _ _ (cyclicGeneratorMap_kernel (A := A) u).symm).trans
    ((cyclicGeneratorMap (A := A) u).quotKerEquivOfSurjective (cyclicGeneratorMap_surjective u))

@[simp] theorem cyclicParentEquiv_mk (u : M) (a : A) :
    (cyclicParentEquiv (A := A) u
      (Ideal.Quotient.mk (Module.annihilator A (cyclicModule (A := A) u)) a) : M) = a • u := rfl

theorem cyclicParent_smul (u : M) (a : A) (r : CyclicParent (A := A) u) :
    a • r = Ideal.Quotient.mk (Module.annihilator A (cyclicModule (A := A) u)) a*r :=
  Algebra.smul_def a r

def cyclicParentAugmentation (eps : A →ₐ[K] K) (u : M) (hu : topProjection eps u ≠ 0) :
    CyclicParent (A := A) u →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ eps (fun _ ha => cyclic_annihilator_le_augmentation eps u hu ha)

@[simp] theorem cyclicParentAugmentation_mk (eps : A →ₐ[K] K) (u : M)
    (hu : topProjection eps u ≠ 0) (a : A) :
    cyclicParentAugmentation eps u hu
      (Ideal.Quotient.mk (Module.annihilator A (cyclicModule (A := A) u)) a) = eps a := rfl

def cyclicParentSocleMap (eps : A →ₐ[K] K) (u : M) (hu : topProjection eps u ≠ 0) :
    algebraSocle (cyclicParentAugmentation eps u hu) →ₗ[K]
      moduleSocle (M := cyclicModule (A := A) u) eps := by
  let f := (cyclicParentEquiv (A := A) u).restrictScalars K
  let g := f.toLinearMap.comp
    ((algebraSocle (cyclicParentAugmentation eps u hu)).subtype.restrictScalars K)
  refine g.codRestrict ((moduleSocle (M := cyclicModule (A := A) u) eps).restrictScalars K) ?_
  intro r a ha
  change a • cyclicParentEquiv u r.1=0
  rw [← (cyclicParentEquiv u).map_smul]
  have hz : a • r.1=0 := by
    rw [cyclicParent_smul,mul_comm]
    exact r.2 _ (by rw [cyclicParentAugmentation_mk]; exact ha)
  rw [hz,map_zero]

theorem cyclicParentSocleMap_bijective (eps : A →ₐ[K] K) (u : M)
    (hu : topProjection eps u ≠ 0) :
    Function.Bijective (cyclicParentSocleMap eps u hu) := by
  constructor
  · intro r s h
    apply Subtype.ext
    apply (cyclicParentEquiv (A := A) u).injective
    exact congrArg (fun x : moduleSocle (M := cyclicModule (A := A) u) eps => x.1) h
  · intro v
    let r := (cyclicParentEquiv (A := A) u).symm v.1
    have hr : r ∈ algebraSocle (cyclicParentAugmentation eps u hu) := by
      intro s hs
      obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective s
      have ha : eps a=0 := by rwa [cyclicParentAugmentation_mk] at hs
      apply (cyclicParentEquiv (A := A) u).injective
      rw [map_zero,mul_comm,← cyclicParent_smul,(cyclicParentEquiv u).map_smul]
      change a • (cyclicParentEquiv u) ((cyclicParentEquiv u).symm v.1)=0
      rw [LinearEquiv.apply_symm_apply]
      exact v.2 a ha
    refine ⟨⟨r,hr⟩,?_⟩
    apply Subtype.ext
    exact (cyclicParentEquiv (A := A) u).apply_symm_apply v.1

def cyclicParentSocleEquiv (eps : A →ₐ[K] K) (u : M) (hu : topProjection eps u ≠ 0) :
    algebraSocle (cyclicParentAugmentation eps u hu) ≃ₗ[K]
      moduleSocle (M := cyclicModule (A := A) u) eps :=
  LinearEquiv.ofBijective (cyclicParentSocleMap eps u hu) (cyclicParentSocleMap_bijective eps u hu)

theorem cyclicParent_socle_finrank_of_full_action [FiniteDimensional K A]
    [FiniteDimensional K M] (eps : A →ₐ[K] K)
    (hfull : Function.Surjective (socleAction (M := M) eps)) (u : M)
    (hu : topProjection eps u ≠ 0) :
    finrank K (algebraSocle (cyclicParentAugmentation eps u hu)) =
      finrank K (moduleSocle (M := M) eps) :=
  (cyclicParentSocleEquiv eps u hu).finrank_eq.trans
    (cyclic_socle_finrank_of_full_action eps hfull u hu)

end Gerstenhaber.FourBlocks.MinimalSource
