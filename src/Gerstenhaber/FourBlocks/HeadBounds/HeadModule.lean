module

public import Gerstenhaber.FourBlocks.MinimalSource.RestrictedBudget
public import Gerstenhaber.FourBlocks.SmallHeads.RelationError

/-! The actual head M/tM and its top. Every map in this file preserves
the original A-action; no small-head model is substituted for M/tM. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.FourBlocks.HeadBounds

open Module LinearMap
open Gerstenhaber.FourBlocks.MinimalSource

variable {K A M N : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
  [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]

def tImage (t : A) : Submodule A M :=
  (t • (LinearMap.id : M →ₗ[A] M)).range

abbrev ActualHead (t : A) := M ⧸ tImage (M := M) t

def headProjection (t : A) : M →ₗ[A] ActualHead (M := M) t := (tImage t).mkQ

theorem headProjection_surjective (t : A) :
    Function.Surjective (headProjection (M := M) t) := (tImage t).mkQ_surjective

theorem head_t_zero (t : A) (q : ActualHead (M := M) t) : t • q = 0 := by
  obtain ⟨x,rfl⟩ := headProjection_surjective t q
  exact (Submodule.Quotient.mk_eq_zero (tImage t)).mpr ⟨x,rfl⟩

theorem tImage_restrictScalars (t : A) :
    (tImage (M := M) t).restrictScalars K = (Algebra.lsmul K K M t).range := by
  ext x
  rfl

theorem actualHead_finrank [FiniteDimensional K M] (t : A) :
    finrank K (ActualHead (M := M) t) = finrank K (LinearMap.ker (Algebra.lsmul K K M t)) := by
  calc
    finrank K (ActualHead (M := M) t) =
        finrank K (M ⧸ (tImage t).restrictScalars K) :=
      (Submodule.Quotient.restrictScalarsEquiv K (tImage t)).finrank_eq.symm
    _ = finrank K (LinearMap.ker (Algebra.lsmul K K M t)) := by
      rw [tImage_restrictScalars]
      exact (finrank_ker_eq_quotient_range _).symm

omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
theorem radical_map_le (eps : A →ₐ[K] K) (q : M →ₗ[A] N) :
    (moduleRadical (M := M) eps).map q ≤ moduleRadical (M := N) eps := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,x,rfl⟩
  change q (a • x) ∈ moduleRadical eps
  rw [q.map_smul]
  exact smul_mem_moduleRadical eps a ha (q x)

omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
theorem radical_map_eq_of_surjective (eps : A →ₐ[K] K)
    (q : M →ₗ[A] N) (hq : Function.Surjective q) :
    (moduleRadical (M := M) eps).map q = moduleRadical (M := N) eps := by
  apply le_antisymm (radical_map_le eps q)
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,y,rfl⟩
  obtain ⟨x,rfl⟩ := hq y
  exact Submodule.mem_map.mpr ⟨a • x,smul_mem_moduleRadical eps a ha x,q.map_smul a x⟩

omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
def actualTopMap (eps : A →ₐ[K] K) (q : M →ₗ[A] N) :
    Top (M := M) eps →ₗ[A] Top (M := N) eps :=
  (moduleRadical eps).mapQ (moduleRadical eps) q
    (Submodule.map_le_iff_le_comap.mp (radical_map_le eps q))

omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
@[simp] theorem actualTopMap_mk (eps : A →ₐ[K] K) (q : M →ₗ[A] N) (x : M) :
    actualTopMap eps q ((moduleRadical eps).mkQ x) = (moduleRadical eps).mkQ (q x) := rfl

omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
theorem actualTopMap_surjective (eps : A →ₐ[K] K)
    (q : M →ₗ[A] N) (hq : Function.Surjective q) :
    Function.Surjective (actualTopMap eps q) := by
  intro z
  obtain ⟨y,rfl⟩ := (moduleRadical (M := N) eps).mkQ_surjective z
  obtain ⟨x,rfl⟩ := hq y
  exact ⟨(moduleRadical eps).mkQ x,rfl⟩

omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
theorem actualTopMap_injective (eps : A →ₐ[K] K)
    (q : M →ₗ[A] N) (hq : Function.Surjective q)
    (hker : q.ker ≤ moduleRadical (M := M) eps) :
    Function.Injective (actualTopMap eps q) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  obtain ⟨x,rfl⟩ := (moduleRadical (M := M) eps).mkQ_surjective z
  have hx : q x ∈ moduleRadical (M := N) eps :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  rw [← radical_map_eq_of_surjective eps q hq] at hx
  obtain ⟨y,hy,hyx⟩ := Submodule.mem_map.mp hx
  have hxy : x-y ∈ q.ker := by
    rw [LinearMap.mem_ker,map_sub,hyx,sub_self]
  have hrad : x ∈ moduleRadical (M := M) eps := by
    have h := (moduleRadical eps).add_mem (hker hxy) hy
    simpa only [sub_add_cancel] using h
  exact (Submodule.Quotient.mk_eq_zero _).mpr hrad

omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
def actualTopEquivOfSurjective (eps : A →ₐ[K] K)
    (q : M →ₗ[A] N) (hq : Function.Surjective q)
    (hker : q.ker ≤ moduleRadical (M := M) eps) :
    Top (M := M) eps ≃ₗ[A] Top (M := N) eps :=
  LinearEquiv.ofBijective (actualTopMap eps q)
    ⟨actualTopMap_injective eps q hq hker,actualTopMap_surjective eps q hq⟩

omit [Module K M] [IsScalarTower K A M] in
theorem tImage_le_radical (eps : A →ₐ[K] K) (t : A) (ht : eps t=0) :
    tImage (M := M) t ≤ moduleRadical eps := by
  rintro _ ⟨x,rfl⟩
  exact smul_mem_moduleRadical eps t ht x

def headTopEquiv (eps : A →ₐ[K] K) (t : A) (ht : eps t=0) :
    Top (M := M) eps ≃ₗ[K] Top (M := ActualHead (M := M) t) eps :=
  (actualTopEquivOfSurjective eps (headProjection t) (headProjection_surjective t) (by
    change (tImage t).mkQ.ker ≤ moduleRadical eps
    rw [Submodule.ker_mkQ]
    exact tImage_le_radical eps t ht)).restrictScalars K

omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
theorem ideal_error_preimage (q : M →ₗ[A] N) (hq : Function.Surjective q)
    (J : Ideal A) (x : M) (hx : q x ∈ J • (⊤ : Submodule A N)) :
    x ∈ J • (⊤ : Submodule A M) ⊔ q.ker := by
  have he : (J • (⊤ : Submodule A M)).map q = J • (⊤ : Submodule A N) := by
    rw [Submodule.map_smul'',Submodule.map_top,LinearMap.range_eq_top.mpr hq]
  rw [← he] at hx
  obtain ⟨y,hy,hyx⟩ := Submodule.mem_map.mp hx
  apply Submodule.mem_sup.mpr
  refine ⟨y,hy,x-y,?_,?_⟩
  · rw [LinearMap.mem_ker,map_sub,hyx,sub_self]
  · abel

theorem head_relation_error_membership (J : Ideal A) (t f g : A) (u v : M)
    (herror : headProjection t (f • u+g • v) ∈
      J • (⊤ : Submodule A (ActualHead (M := M) t))) :
    f • u+g • v ∈ J • (⊤ : Submodule A M) ⊔
      Gerstenhaber.FourBlocks.SmallHeads.scalarRange t := by
  have h := ideal_error_preimage (headProjection t) (headProjection_surjective t)
    J (f • u+g • v) herror
  change _ ∈ _ ⊔ (tImage t).mkQ.ker at h
  rw [Submodule.ker_mkQ] at h
  exact h

theorem actual_head_relation_lift (J : Ideal A) (t f0 g0 : A) (u v : M)
    (hgen : Submodule.span A {u,v}=⊤)
    (herror : headProjection t (f0 • u+g0 • v) ∈
      J • (⊤ : Submodule A (ActualHead (M := M) t))) :
    ∃ f2 ∈ J, ∃ g2 ∈ J, ∃ p q : A,
      (f0-f2-t*p) • u+(g0-g2-t*q) • v=0 :=
  Gerstenhaber.FourBlocks.SmallHeads.absorb_relation_error J t f0 g0 u v hgen
    (head_relation_error_membership J t f0 g0 u v herror)

end Gerstenhaber.FourBlocks.HeadBounds
