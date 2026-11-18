module

public import Gerstenhaber.FourBlocks.MinimalSource.MinimalCounterexample

/-!
Actual cyclic evaluation for one and the same maximum-rank vector.
The maximum and a prescribed nonzero head coefficient can be chosen
simultaneously. Full socle action and Flanders nesting are then proved
for this vector, rather than assumed for different maximum notions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap

variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

def cyclicModule (u : M) : Submodule A M := Submodule.span A {u}

def cyclicEvaluation : M →ₗ[K] A →ₗ[K] M :=
  (Algebra.lsmul K K M).toLinearMap.flip

@[simp] theorem cyclicEvaluation_apply (u : M) (a : A) :
    cyclicEvaluation (K := K) (A := A) u a=a • u := rfl

theorem cyclicEvaluation_range (u : M) :
    LinearMap.range (cyclicEvaluation (K := K) (A := A) u) = (cyclicModule (A := A) u).restrictScalars K := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact Submodule.mem_span_singleton.mpr ⟨a,rfl⟩
  · intro hx
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨a,ha⟩

def IsMaximalCyclic (u : M) : Prop :=
  ∀ v : M, finrank K (LinearMap.range (cyclicEvaluation (K := K) (A := A) v)) ≤
    finrank K (LinearMap.range (cyclicEvaluation (K := K) (A := A) u))

theorem exists_maximal_cyclic [FiniteDimensional K M] :
    ∃ u : M, IsMaximalCyclic (K := K) (A := A) u :=
  exists_maximal_slice (cyclicEvaluation (K := K) (A := A) (M := M))

theorem cyclicEvaluation_rank_pos [FiniteDimensional K M] (v : M) (hv : v ≠ 0) :
    0 < finrank K (LinearMap.range (cyclicEvaluation (K := K) (A := A) v)) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨v,⟨1,one_smul A v⟩⟩,?_⟩
  intro h
  exact hv (congrArg Subtype.val h)

/-- The maximum slice can be chosen in any prescribed nonzero linear
functional chart. This is the finite-pencil form of the usual open-chart
argument and uses no algebraic-geometric genericity hypothesis. -/
theorem exists_maximal_cyclic_of_functional [Infinite K] [FiniteDimensional K A]
    [FiniteDimensional K M] (ell : Module.Dual K M) (hell : ell ≠ 0) :
    ∃ u : M, ell u ≠ 0 ∧ IsMaximalCyclic (K := K) (A := A) u := by
  classical
  obtain ⟨u,hu⟩ := exists_maximal_cyclic (K := K) (A := A) (M := M)
  by_cases hzero : ell u=0
  · obtain ⟨v,hv⟩ := LinearMap.surjective hell (1 : K)
    have hv0 : v ≠ 0 := by intro h; rw [h,map_zero] at hv; exact zero_ne_one hv
    have hpos : 0 < finrank K (LinearMap.range (cyclicEvaluation (K := K) (A := A) u)) :=
      (cyclicEvaluation_rank_pos (K := K) (A := A) v hv0).trans_le (hu v)
    have hex : ∃ a : K, a ≠ 0 ∧
        finrank K (LinearMap.range (cyclicEvaluation (K := K) (A := A) (u+a • v))) =
          finrank K (LinearMap.range (cyclicEvaluation (K := K) (A := A) u)) := by
      by_contra h
      push Not at h
      have hbound (a : K) (ha : a ≠ 0) :
          finrank K (LinearMap.range (cyclicEvaluation (K := K) (A := A) u+
            a • cyclicEvaluation (K := K) (A := A) v)) ≤
              finrank K (LinearMap.range (cyclicEvaluation (K := K) (A := A) u))-1 := by
        have hle := hu (u+a • v)
        have hne := h a ha
        rw [map_add,map_smul] at hle hne
        omega
      have hle := finrank_range_pencil_specialize
        (cyclicEvaluation (K := K) (A := A) u) (cyclicEvaluation (K := K) (A := A) v) _ hbound
      omega
    obtain ⟨a,ha,hrank⟩ := hex
    refine ⟨u+a • v,?_,fun w => (hu w).trans_eq hrank.symm⟩
    simpa only [map_add,map_smul,hzero,hv,smul_eq_mul,mul_one,zero_add] using ha
  · exact ⟨u,hzero,hu⟩

theorem exists_maximal_cyclic_with_top_functional [Infinite K] [FiniteDimensional K A]
    [FiniteDimensional K M] (eps : A →ₐ[K] K)
    (phi : Module.Dual K (Top (M := M) eps)) (hphi : phi ≠ 0) :
    ∃ u : M, phi (topProjection eps u) ≠ 0 ∧ IsMaximalCyclic (K := K) (A := A) u := by
  apply exists_maximal_cyclic_of_functional (A := A) (phi.comp (topProjection eps))
  intro h
  apply hphi
  apply LinearMap.ext
  intro q
  obtain ⟨x,rfl⟩ := topProjection_surjective eps q
  exact LinearMap.congr_fun h x

/-- Full socle action puts every socle vector in the actual cyclic
module of every nonzero top vector. -/
theorem socle_le_cyclic_of_full_action (eps : A →ₐ[K] K)
    (hfull : Function.Surjective (socleAction (M := M) eps)) (u : M)
    (hu : topProjection eps u ≠ 0) : moduleSocle (M := M) eps ≤ cyclicModule (A := A) u := by
  classical
  obtain ⟨phi,hphi⟩ := Module.Projective.exists_dual_eq_one K hu
  intro v hv
  let v' : moduleSocle (M := M) eps := ⟨v,hv⟩
  obtain ⟨s,hs⟩ := hfull (phi.smulRight v')
  apply Submodule.mem_span_singleton.mpr
  refine ⟨s.1,?_⟩
  have h := congrArg (fun f => (f (topProjection eps u) : M)) hs
  simp only [LinearMap.smulRight_apply,hphi,one_smul] at h
  change s.1 • u=v at h
  exact h

def cyclicSocleInclusion (eps : A →ₐ[K] K) (u : M) :
    moduleSocle (M := cyclicModule (A := A) u) eps →ₗ[K] moduleSocle (M := M) eps where
  toFun v := ⟨v.1.1,fun a ha => congrArg Subtype.val (v.2 a ha)⟩
  map_add' := by intro x y; rfl
  map_smul' := by intro k x; rfl

theorem cyclicSocleInclusion_injective (eps : A →ₐ[K] K) (u : M) :
    Function.Injective (cyclicSocleInclusion (K := K) eps u) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : moduleSocle (M := M) eps => (z : M)) h

def cyclicSocleEquiv (eps : A →ₐ[K] K) (u : M)
    (hsoc : moduleSocle (M := M) eps ≤ cyclicModule (A := A) u) :
    moduleSocle (M := cyclicModule (A := A) u) eps ≃ₗ[K] moduleSocle (M := M) eps :=
  LinearEquiv.ofBijective (cyclicSocleInclusion eps u) ⟨cyclicSocleInclusion_injective eps u,by
    intro v
    exact ⟨⟨⟨v.1,hsoc v.2⟩,fun a ha => Subtype.ext (v.2 a ha)⟩,rfl⟩⟩

theorem cyclic_socle_finrank_of_full_action [FiniteDimensional K M]
    (eps : A →ₐ[K] K) (hfull : Function.Surjective (socleAction (M := M) eps))
    (u : M) (hu : topProjection eps u ≠ 0) :
    finrank K (moduleSocle (M := cyclicModule (A := A) u) eps) =
      finrank K (moduleSocle (M := M) eps) :=
  (cyclicSocleEquiv eps u (socle_le_cyclic_of_full_action eps hfull u hu)).finrank_eq

theorem maximal_cyclic_annihilator_smul_mem [Infinite K] [FiniteDimensional K A]
    [FiniteDimensional K M] (u : M) (hu : IsMaximalCyclic (K := K) (A := A) u)
    (a : A) (ha : a ∈ Module.annihilator A (cyclicModule (A := A) u)) (v : M) :
    a • v ∈ cyclicModule (A := A) u := by
  have hau : a • u=0 :=
    (mem_annihilator_submodule_iff (cyclicModule (A := A) u) a).mp ha u
      (Submodule.mem_span_singleton_self u)
  have hin : cyclicEvaluation (K := K) (A := A) v a ∈ LinearMap.range (cyclicEvaluation (K := K) (A := A) u) := by
    apply maximal_rank_pencil_ker_range _ _ _ a hau
    intro k
    have h := hu (u+k • v)
    rw [map_add,map_smul] at h
    exact h
  rw [cyclicEvaluation_range] at hin
  exact hin

/-- The actual kernel of the cyclic parent kills the actual remaining
quotient. This is derived for the same chosen maximum vector. -/
theorem maximal_cyclic_annihilator_le_quotient [Infinite K] [FiniteDimensional K A]
    [FiniteDimensional K M] (u : M) (hu : IsMaximalCyclic (K := K) (A := A) u) :
    Module.annihilator A (cyclicModule (A := A) u) ≤ Module.annihilator A (M ⧸ cyclicModule (A := A) u) := by
  intro a ha
  apply (mem_annihilator_quotient_iff (cyclicModule (A := A) u) a).mpr
  exact maximal_cyclic_annihilator_smul_mem u hu a ha

theorem cyclic_annihilator_le_augmentation (eps : A →ₐ[K] K) (u : M)
    (hu : topProjection eps u ≠ 0) :
    Module.annihilator A (cyclicModule (A := A) u) ≤ augmentationIdeal eps := by
  intro a ha
  have hau : a • u=0 :=
    (mem_annihilator_submodule_iff (cyclicModule (A := A) u) a).mp ha u
      (Submodule.mem_span_singleton_self u)
  have hz : eps a • topProjection eps u=0 := by
    rw [← topProjection_smul,hau,map_zero]
  exact (smul_eq_zero.mp hz).resolve_right hu

/-- One actual vector satisfies the prescribed head chart, maximum
cyclic rank, full-socle containment and actual annihilator nesting. -/
theorem exists_full_socle_maximal_parent [Infinite K] [FiniteDimensional K A]
    [FiniteDimensional K M] (eps : A →ₐ[K] K)
    (hfull : Function.Surjective (socleAction (M := M) eps))
    (phi : Module.Dual K (Top (M := M) eps)) (hphi : phi ≠ 0) :
    ∃ u : M, phi (topProjection eps u) ≠ 0 ∧ IsMaximalCyclic (K := K) (A := A) u ∧
      moduleSocle (M := M) eps ≤ cyclicModule (A := A) u ∧
      Module.annihilator A (cyclicModule (A := A) u) ≤
        Module.annihilator A (M ⧸ cyclicModule (A := A) u) := by
  obtain ⟨u,hchart,hmax⟩ := exists_maximal_cyclic_with_top_functional eps phi hphi
  have htop : topProjection eps u ≠ 0 := by
    intro hzero
    exact hchart (by rw [hzero,map_zero])
  exact ⟨u,hchart,hmax,socle_le_cyclic_of_full_action eps hfull u htop,
    maximal_cyclic_annihilator_le_quotient u hmax⟩

end Gerstenhaber.FourBlocks.MinimalSource
