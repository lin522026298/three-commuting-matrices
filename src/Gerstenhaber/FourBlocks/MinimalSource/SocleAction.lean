module

public import Gerstenhaber.FourBlocks.MinimalSource.SocleTensor
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
Actual radical, socle and socle action for a commutative augmented algebra.
The action map and its injectivity are constructed from multiplication
and faithfulness, not assumed as a tensor-space hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap

variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M]

/-- The actual mM, where m is the kernel of the given augmentation. -/
def moduleRadical (eps : A →ₐ[K] K) : Submodule A M :=
  Submodule.span A {z : M | ∃ a : A, eps a = 0 ∧ ∃ x : M, a • x = z}

theorem smul_mem_moduleRadical (eps : A →ₐ[K] K) (a : A) (ha : eps a = 0) (x : M) :
    a • x ∈ moduleRadical eps :=
  Submodule.subset_span ⟨a,ha,x,rfl⟩

/-- The actual module socle killed by the augmentation ideal. -/
def moduleSocle (eps : A →ₐ[K] K) : Submodule A M where
  carrier := {x | ∀ a : A, eps a = 0 → a • x = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy a ha; rw [smul_add,hx a ha,hy a ha,add_zero]
  smul_mem' := by
    intro r x hx a ha
    rw [← mul_smul,mul_comm a r,mul_smul,hx a ha,smul_zero]

@[simp] theorem mem_moduleSocle (eps : A →ₐ[K] K) (x : M) :
    x ∈ moduleSocle eps ↔ ∀ a : A, eps a = 0 → a • x = 0 := Iff.rfl

/-- The actual algebra socle Ann_A(ker eps). -/
def algebraSocle (eps : A →ₐ[K] K) : Ideal A where
  carrier := {s | ∀ a : A, eps a = 0 → s*a = 0}
  zero_mem' := by simp
  add_mem' := by intro s t hs ht a ha; rw [add_mul,hs a ha,ht a ha,add_zero]
  smul_mem' := by
    intro r s hs a ha
    change (r*s)*a=0
    rw [mul_assoc,hs a ha,mul_zero]

@[simp] theorem mem_algebraSocle (eps : A →ₐ[K] K) (s : A) :
    s ∈ algebraSocle eps ↔ ∀ a : A, eps a = 0 → s*a=0 := Iff.rfl

abbrev Top (eps : A →ₐ[K] K) := M ⧸ moduleRadical (M := M) eps

def socleMul (eps : A →ₐ[K] K) (s : algebraSocle eps) :
    M →ₗ[A] moduleSocle (M := M) eps where
  toFun x := ⟨s.1 • x,by
    intro a ha
    rw [← mul_smul,mul_comm a s.1,s.2 a ha,zero_smul]⟩
  map_add' := by intro x y; apply Subtype.ext; exact smul_add _ _ _
  map_smul' := by
    intro a x
    apply Subtype.ext
    change s.1 • (a • x) = a • (s.1 • x)
    rw [← mul_smul,← mul_smul,mul_comm]

theorem moduleRadical_le_ker_socleMul (eps : A →ₐ[K] K) (s : algebraSocle eps) :
    moduleRadical eps ≤ LinearMap.ker (socleMul (M := M) eps s) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,x,rfl⟩
  apply Subtype.ext
  change s.1 • (a • x) = 0
  rw [← mul_smul,s.2 a ha,zero_smul]

variable [Module K M] [IsScalarTower K A M]

def socleAction (eps : A →ₐ[K] K) :
    algebraSocle eps →ₗ[K] (Top (M := M) eps →ₗ[K] moduleSocle (M := M) eps) where
  toFun s := ((moduleRadical eps).liftQ (socleMul eps s)
    (moduleRadical_le_ker_socleMul eps s)).restrictScalars K
  map_add' := by
    intro s t
    apply LinearMap.ext
    intro q
    obtain ⟨x,rfl⟩ := (moduleRadical (M := M) eps).mkQ_surjective q
    apply Subtype.ext
    change (s.1+t.1) • x = s.1 • x+t.1 • x
    exact add_smul _ _ _
  map_smul' := by
    intro c s
    apply LinearMap.ext
    intro q
    obtain ⟨x,rfl⟩ := (moduleRadical (M := M) eps).mkQ_surjective q
    apply Subtype.ext
    change (c • s.1) • x = c • (s.1 • x)
    exact smul_assoc _ _ _

@[simp] theorem socleAction_mk (eps : A →ₐ[K] K) (s : algebraSocle eps) (x : M) :
    (socleAction (M := M) eps s ((moduleRadical eps).mkQ x) : M) = s.1 • x := rfl

theorem socleAction_injective [FaithfulSMul A M] (eps : A →ₐ[K] K) :
    Function.Injective (socleAction (M := M) eps) := by
  intro s t hst
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := M)
  intro x
  have h := congrArg (fun F => (F ((moduleRadical eps).mkQ x) : M)) hst
  exact h

theorem algebraSocle_eq_annihilator (eps : A →ₐ[K] K) :
    algebraSocle eps = Module.annihilator A (RingHom.ker eps.toRingHom) := by
  ext s
  rw [mem_algebraSocle,Module.mem_annihilator]
  constructor
  · intro hs a
    apply Subtype.ext
    exact hs a.1 a.2
  · intro hs a ha
    exact congrArg Subtype.val (hs ⟨a,ha⟩)

def topProjection (eps : A →ₐ[K] K) : M →ₗ[K] Top (M := M) eps :=
  (moduleRadical eps).mkQ.restrictScalars K

theorem topProjection_surjective (eps : A →ₐ[K] K) :
    Function.Surjective (topProjection (M := M) eps) :=
  (moduleRadical eps).mkQ_surjective

theorem sub_eps_smul_mem_radical (eps : A →ₐ[K] K) (a : A) (x : M) :
    a • x - eps a • x ∈ moduleRadical eps := by
  have h := smul_mem_moduleRadical eps (a-algebraMap K A (eps a)) (by simp) x
  simpa only [sub_smul,IsScalarTower.algebraMap_smul] using h

theorem topProjection_smul (eps : A →ₐ[K] K) (a : A) (x : M) :
    topProjection eps (a • x) = eps a • topProjection eps x := by
  have h := (Submodule.Quotient.mk_eq_zero (moduleRadical eps)).mpr
    (sub_eps_smul_mem_radical eps a x)
  change topProjection eps (a • x-eps a • x) = 0 at h
  rw [map_sub,(topProjection eps).map_smul (eps a) x] at h
  exact sub_eq_zero.mp h

theorem smul_eq_eps_smul_of_mem_socle (eps : A →ₐ[K] K) (x : M)
    (hx : x ∈ moduleSocle eps) (a : A) : a • x = eps a • x := by
  have h := hx (a-algebraMap K A (eps a)) (by simp)
  rw [sub_smul,IsScalarTower.algebraMap_smul] at h
  exact sub_eq_zero.mp h

/-- The literal inverse image of a top hyperplane, with A-stability
proved from the augmentation action on the actual top. -/
def topHyperplane (eps : A →ₐ[K] K) (φ : Module.Dual K (Top (M := M) eps)) :
    Submodule A M where
  carrier := {x | φ (topProjection eps x) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change φ (topProjection eps x) = 0 at hx
    change φ (topProjection eps y) = 0 at hy
    change φ (topProjection eps (x+y)) = 0
    rw [map_add,map_add,hx,hy,add_zero]
  smul_mem' := by
    intro a x hx
    change φ (topProjection eps x) = 0 at hx
    change φ (topProjection eps (a • x)) = 0
    rw [topProjection_smul,map_smul,hx,smul_zero]

@[simp] theorem mem_topHyperplane (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) (x : M) :
    x ∈ topHyperplane eps φ ↔ φ (topProjection eps x) = 0 := Iff.rfl

theorem moduleRadical_le_topHyperplane (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) : moduleRadical eps ≤ topHyperplane eps φ := by
  intro x hx
  have h : topProjection eps x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx
  change φ (topProjection eps x) = 0
  rw [h,map_zero]

/-- The literal scalar line through a socle vector, with its actual
A-module stability. -/
def socleLine (eps : A →ₐ[K] K) (v : moduleSocle (M := M) eps) : Submodule A M where
  carrier := {x | ∃ c : K, c • v.1 = x}
  zero_mem' := ⟨0,zero_smul _ _⟩
  add_mem' := by
    rintro x y ⟨a,rfl⟩ ⟨b,rfl⟩
    exact ⟨a+b,add_smul _ _ _⟩
  smul_mem' := by
    rintro a x ⟨c,rfl⟩
    refine ⟨c*eps a,?_⟩
    rw [smul_comm a c,smul_eq_eps_smul_of_mem_socle eps v.1 v.2,smul_smul]

@[simp] theorem mem_socleLine (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) (x : M) :
    x ∈ socleLine eps v ↔ ∃ c : K, c • v.1 = x := Iff.rfl

end Gerstenhaber.FourBlocks.MinimalSource
