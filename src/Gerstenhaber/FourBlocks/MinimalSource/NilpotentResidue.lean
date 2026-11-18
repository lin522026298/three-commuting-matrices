module

public import Gerstenhaber.FourBlocks.MinimalSource.AnnihilatorFibers
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
Nonzero top and socle are derived from the actual nilpotent augmentation
ideal. They are not assumed as nonzero-fiber hypotheses in the source
budget. This uses ordinary finite powers of the ideal action.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap

variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M]

def augmentationIdeal (eps : A →ₐ[K] K) : Ideal A := RingHom.ker eps.toRingHom

theorem faithful_module_nontrivial [FaithfulSMul A M] (eps : A →ₐ[K] K) : Nontrivial M := by
  classical
  by_contra h
  let : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
  have hA : (1 : A)=0 := eq_of_smul_eq_smul (α := M) (fun _ => Subsingleton.elim _ _)
  have hK : (1 : K)=0 := by simpa only [map_one,map_zero] using congrArg eps hA
  exact one_ne_zero hK

theorem moduleRadical_eq_ideal_smul_top (eps : A →ₐ[K] K) :
    moduleRadical (M := M) eps = augmentationIdeal eps • (⊤ : Submodule A M) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,x,rfl⟩
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · apply Submodule.smul_le.mpr
    intro a ha x _
    exact smul_mem_moduleRadical eps a ha x

theorem top_nontrivial_of_nilpotent [Nontrivial M] (eps : A →ₐ[K] K)
    (hnil : IsNilpotent (augmentationIdeal eps)) : Nontrivial (Top (M := M) eps) := by
  apply Submodule.Quotient.nontrivial_iff.mpr
  intro hrad
  have hp (n : ℕ) : (augmentationIdeal eps)^n • (⊤ : Submodule A M) = ⊤ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',Submodule.mul_smul,ih,← moduleRadical_eq_ideal_smul_top,hrad]
  obtain ⟨n,hn⟩ := hnil
  have h := hp n
  rw [hn,zero_smul] at h
  exact bot_ne_top h

theorem socle_nontrivial_of_nilpotent [Nontrivial M] (eps : A →ₐ[K] K)
    (hnil : IsNilpotent (augmentationIdeal eps)) : Nontrivial (moduleSocle (M := M) eps) := by
  classical
  let I := augmentationIdeal eps
  let P : ℕ → Prop := fun n => I^n • (⊤ : Submodule A M) = ⊥
  have hex : ∃ n, P n := by
    obtain ⟨n,hn⟩ := hnil
    exact ⟨n,by simp [P,I,hn]⟩
  let n := Nat.find hex
  have hn : 0<n := by
    by_contra h
    have hn0 : n=0 := by omega
    have hzero := Nat.find_spec hex
    change P n at hzero
    rw [hn0] at hzero
    simp [P] at hzero
  have hprev : I^(n-1) • (⊤ : Submodule A M) ≠ ⊥ := by
    intro hzero
    have hle : n ≤ n-1 := Nat.find_min' hex hzero
    omega
  obtain ⟨y,hy,hy0⟩ := (Submodule.ne_bot_iff _).mp hprev
  have hsoc : y ∈ moduleSocle eps := by
    intro a ha
    have hmem : a • y ∈ I • (I^(n-1) • (⊤ : Submodule A M)) :=
      Submodule.smul_mem_smul ha hy
    have heq : I • (I^(n-1) • (⊤ : Submodule A M)) = I^n • (⊤ : Submodule A M) := by
      rw [← Submodule.mul_smul,← pow_succ']
      have he : n-1+1=n := by omega
      rw [he]
    rw [heq,Nat.find_spec hex] at hmem
    exact hmem
  exact ⟨⟨⟨y,hsoc⟩,0,fun h => hy0 (congrArg Subtype.val h)⟩⟩

end Gerstenhaber.FourBlocks.MinimalSource
