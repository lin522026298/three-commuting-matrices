module

public import Gerstenhaber.FourBlocks.MinimalSource.ActualBudget
public import Gerstenhaber.FourBlocks.MinimalSource.BlockClosure

/-!
An explicit restricted-class safety interface.  All modules in this file
are in the same universe as the field, so literal submodules and
quotients remain inside its quantifier.  A global minimum-counterexample
argument must still discharge this predicate from the given three
generators; no such theorem is assumed here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap

/-- Safety below n for modules with at most r kernels of the fixed
operator t, always measured using their actual acting image algebra. -/
def RestrictedSafeBelow (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    (t : A) (n r : ℕ) : Prop :=
  ∀ (N : Type u) [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
    [FiniteDimensional K N],
    finrank K N<n → finrank K (LinearMap.ker (Algebra.lsmul K K N t)) ≤ r →
      finrank K (actualActionImage (K := K) (A := A) (M := N)) ≤ finrank K N

variable {K A M : Type u} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

theorem submodule_t_kernel_finrank_le [FiniteDimensional K M]
    (P : Submodule A M) (t : A) :
    finrank K (LinearMap.ker (Algebra.lsmul K K P t)) ≤
      finrank K (LinearMap.ker (Algebra.lsmul K K M t)) :=
  finrank_ker_le_of_injective_intertwining _ _ (P.subtype.restrictScalars K)
    P.injective_subtype (fun _ => rfl)

theorem quotient_t_kernel_finrank_le [FiniteDimensional K M]
    (P : Submodule A M) (t : A) :
    finrank K (LinearMap.ker (Algebra.lsmul K K (M ⧸ P) t)) ≤
      finrank K (LinearMap.ker (Algebra.lsmul K K M t)) := by
  let : FiniteDimensional K (M ⧸ P) :=
    FiniteDimensional.of_surjective (P.mkQ.restrictScalars K) P.mkQ_surjective
  exact finrank_ker_le_of_surjective_intertwining _ _ (P.mkQ.restrictScalars K)
    P.mkQ_surjective (fun _ => rfl)

theorem socle_finrank_le_t_kernel [FiniteDimensional K M]
    (eps : A →ₐ[K] K) (t : A) (ht : eps t=0) :
    finrank K (moduleSocle (M := M) eps) ≤
      finrank K (LinearMap.ker (Algebra.lsmul K K M t)) := by
  have hle : (moduleSocle (M := M) eps).restrictScalars K ≤
      LinearMap.ker (Algebra.lsmul K K M t) := fun _ hx => hx t ht
  exact Submodule.finrank_mono hle

theorem top_finrank_le_t_kernel [FiniteDimensional K M]
    (eps : A →ₐ[K] K) (t : A) (ht : eps t=0) :
    finrank K (Top (M := M) eps) ≤
      finrank K (LinearMap.ker (Algebra.lsmul K K M t)) := by
  let T := Algebra.lsmul K K M t
  let p : (M ⧸ LinearMap.range T) →ₗ[K] Top (M := M) eps :=
    (LinearMap.range T).liftQ (topProjection eps) (by
      rintro _ ⟨x,rfl⟩
      exact (Submodule.Quotient.mk_eq_zero (moduleRadical eps)).mpr
        (smul_mem_moduleRadical eps t ht x))
  have hp : Function.Surjective p := by
    intro q
    obtain ⟨x,rfl⟩ := topProjection_surjective eps q
    exact ⟨(LinearMap.range T).mkQ x,rfl⟩
  have h := LinearMap.finrank_le_finrank_of_surjective hp
  rw [← finrank_ker_eq_quotient_range] at h
  exact h

/-- Apply restricted-class safety to the two actual annihilator
families.  Their being shorter and their kernel bounds are all proved
here, rather than passed in as new family hypotheses. -/
theorem actual_socle_budget_of_restricted_safety [Infinite K]
    [FiniteDimensional K A] [FiniteDimensional K M] [FaithfulSMul A M]
    (eps : A →ₐ[K] K) (t : A) (r e : ℕ)
    (hdim : finrank K A=finrank K M+e)
    (hnil : IsNilpotent (augmentationIdeal eps))
    (hr : finrank K (LinearMap.ker (Algebra.lsmul K K M t)) ≤ r)
    (hsafe : RestrictedSafeBelow K A t (finrank K M) r) :
    e+1 ≤ finrank K (Top (M := M) eps) ∧
      e+1 ≤ finrank K (moduleSocle (M := M) eps) ∧
      (e+1)*(finrank K (Top (M := M) eps)+finrank K (moduleSocle (M := M) eps)-(e+1)) ≤
        finrank K (algebraSocle eps) := by
  apply actual_socle_budget_of_shorter_safety eps e hdim hnil
  · intro φ hφ
    let : FiniteDimensional K (topHyperplane eps φ) :=
      FiniteDimensional.of_injective ((topHyperplane eps φ).subtype.restrictScalars K)
        (topHyperplane eps φ).injective_subtype
    have hlen := topHyperplane_finrank_add_one eps φ hφ
    exact hsafe (topHyperplane eps φ) (by omega)
      ((submodule_t_kernel_finrank_le _ t).trans hr)
  · intro v hv
    let : FiniteDimensional K (M ⧸ socleLine eps v) :=
      FiniteDimensional.of_surjective ((socleLine eps v).mkQ.restrictScalars K)
        (socleLine eps v).mkQ_surjective
    have hlen := socleLine_quotient_finrank_add_one eps v hv
    exact hsafe (M ⧸ socleLine eps v) (by omega)
      ((quotient_t_kernel_finrank_le _ t).trans hr)

end Gerstenhaber.FourBlocks.MinimalSource
