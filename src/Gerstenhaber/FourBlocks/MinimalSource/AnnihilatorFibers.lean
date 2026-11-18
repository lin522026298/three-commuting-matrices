module

public import Gerstenhaber.FourBlocks.MinimalSource.SocleAction
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
The two actual annihilator families behind the finite socle-tensor
budget.  Submodules and quotients retain their given A-actions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap

variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]

theorem mem_annihilator_submodule_iff (N : Submodule A M) (g : A) :
    g ∈ Module.annihilator A N ↔ ∀ x : M, x ∈ N → g • x = 0 := by
  rw [Module.mem_annihilator]
  constructor
  · intro h x hx
    exact congrArg Subtype.val (h ⟨x,hx⟩)
  · intro h x
    apply Subtype.ext
    exact h x.1 x.2

theorem mem_annihilator_quotient_iff (N : Submodule A M) (g : A) :
    g ∈ Module.annihilator A (M ⧸ N) ↔ ∀ x : M, g • x ∈ N := by
  rw [Module.mem_annihilator]
  constructor
  · intro h x
    exact (Submodule.Quotient.mk_eq_zero N).mp (h (N.mkQ x))
  · intro h q
    obtain ⟨x,rfl⟩ := N.mkQ_surjective q
    exact (Submodule.Quotient.mk_eq_zero N).mpr (h x)

omit [Module K M] [IsScalarTower K A M] in
theorem annihilator_le_algebraSocle_of_radical_le [FaithfulSMul A M]
    (eps : A →ₐ[K] K) (N : Submodule A M) (hN : moduleRadical eps ≤ N) :
    Module.annihilator A N ≤ algebraSocle eps := by
  intro g hg a ha
  apply eq_of_smul_eq_smul (α := M)
  intro x
  rw [zero_smul,mul_smul]
  exact (mem_annihilator_submodule_iff N g).mp hg (a • x)
    (hN (smul_mem_moduleRadical eps a ha x))

theorem socleLine_le_moduleSocle (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) : socleLine eps v ≤ moduleSocle eps := by
  rintro x ⟨c,rfl⟩
  exact ((moduleSocle eps).restrictScalars K).smul_mem c v.2

omit [Module K M] [IsScalarTower K A M] in
theorem quotient_annihilator_le_algebraSocle [FaithfulSMul A M]
    (eps : A →ₐ[K] K) (N : Submodule A M) (hN : N ≤ moduleSocle eps) :
    Module.annihilator A (M ⧸ N) ≤ algebraSocle eps := by
  intro g hg a ha
  apply eq_of_smul_eq_smul (α := M)
  intro x
  rw [zero_smul,mul_smul,smul_comm]
  exact hN ((mem_annihilator_quotient_iff N g).mp hg x) a ha

def socleTensor (eps : A →ₐ[K] K) :
    Submodule K (Top (M := M) eps →ₗ[K] moduleSocle (M := M) eps) :=
  LinearMap.range (socleAction (M := M) eps)

def hyperplaneAnnToSocle [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) :
    Module.annihilator A (topHyperplane eps φ) →ₗ[K] algebraSocle eps where
  toFun g := ⟨g.1,annihilator_le_algebraSocle_of_radical_le eps _
    (moduleRadical_le_topHyperplane eps φ) g.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lineQuotientAnnToSocle [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) :
    Module.annihilator A (M ⧸ socleLine eps v) →ₗ[K] algebraSocle eps where
  toFun g := ⟨g.1,quotient_annihilator_le_algebraSocle eps _
    (socleLine_le_moduleSocle eps v) g.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem hyperplane_ann_action_kills_kernel [FaithfulSMul A M]
    (eps : A →ₐ[K] K) (φ : Module.Dual K (Top (M := M) eps))
    (g : Module.annihilator A (topHyperplane eps φ)) (q : Top (M := M) eps)
    (hq : φ q = 0) : socleAction eps (hyperplaneAnnToSocle eps φ g) q = 0 := by
  obtain ⟨x,rfl⟩ := topProjection_surjective eps q
  apply Subtype.ext
  exact (mem_annihilator_submodule_iff _ _).mp g.2 x hq

theorem line_quotient_ann_action_range [FaithfulSMul A M]
    (eps : A →ₐ[K] K) (v : moduleSocle (M := M) eps)
    (g : Module.annihilator A (M ⧸ socleLine eps v)) (q : Top (M := M) eps) :
    ∃ c : K, c • v = socleAction eps (lineQuotientAnnToSocle eps v g) q := by
  obtain ⟨x,rfl⟩ := topProjection_surjective eps q
  obtain ⟨c,hc⟩ := (mem_annihilator_quotient_iff _ _).mp g.2 x
  exact ⟨c,Subtype.ext hc⟩

section RankOneFactor

variable {U V : Type*} [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]

theorem eq_smulRight_of_kills_kernel (f : U →ₗ[K] V) (φ : Module.Dual K U)
    (u0 : U) (hu0 : φ u0=1) (hker : ∀ u, φ u=0 → f u=0) :
    f = φ.smulRight (f u0) := by
  ext u
  change f u = φ u • f u0
  have hz : φ (u-φ u • u0)=0 := by simp [hu0]
  have h := hker _ hz
  rw [map_sub,map_smul] at h
  exact sub_eq_zero.mp h

theorem eq_smulRight_of_range_line (f : U →ₗ[K] V) (v : V)
    (ψ : Module.Dual K V) (hψ : ψ v=1)
    (hline : ∀ u, ∃ c : K, c • v=f u) : f = (ψ.comp f).smulRight v := by
  ext u
  change f u = ψ (f u) • v
  obtain ⟨c,hc⟩ := hline u
  rw [← hc,map_smul,hψ,smul_eq_mul,mul_one]

end RankOneFactor

def hyperplaneAnnEval [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) (u0 : Top (M := M) eps) :
    Module.annihilator A (topHyperplane eps φ) →ₗ[K] moduleSocle (M := M) eps where
  toFun g := socleAction eps (hyperplaneAnnToSocle eps φ g) u0
  map_add' := by
    intro g h
    change socleAction eps (hyperplaneAnnToSocle eps φ g+hyperplaneAnnToSocle eps φ h) u0 = _
    rw [map_add,LinearMap.add_apply]
  map_smul' := by
    intro c g
    change socleAction eps (c • hyperplaneAnnToSocle eps φ g) u0 = _
    rw [map_smul,LinearMap.smul_apply]
    rfl

theorem hyperplane_ann_factor [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) (u0 : Top (M := M) eps) (hu0 : φ u0=1)
    (g : Module.annihilator A (topHyperplane eps φ)) :
    socleAction eps (hyperplaneAnnToSocle eps φ g) =
      φ.smulRight (hyperplaneAnnEval eps φ u0 g) :=
  eq_smulRight_of_kills_kernel _ φ u0 hu0 (hyperplane_ann_action_kills_kernel eps φ g)

theorem hyperplaneAnnEval_injective [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) (u0 : Top (M := M) eps) (hu0 : φ u0=1) :
    Function.Injective (hyperplaneAnnEval eps φ u0) := by
  intro g h hgh
  have hs := socleAction_injective (M := M) eps (show
      socleAction eps (hyperplaneAnnToSocle eps φ g) =
        socleAction eps (hyperplaneAnnToSocle eps φ h) by
    rw [hyperplane_ann_factor eps φ u0 hu0 g,hyperplane_ann_factor eps φ u0 hu0 h,hgh])
  exact Subtype.ext (congrArg (fun s : algebraSocle eps => (s : A)) hs)

theorem range_hyperplaneAnnEval [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) (u0 : Top (M := M) eps) (hu0 : φ u0=1) :
    LinearMap.range (hyperplaneAnnEval eps φ u0) = fixedFunctionalFiber (socleTensor eps) φ := by
  ext v
  constructor
  · rintro ⟨g,rfl⟩
    rw [mem_fixedFunctionalFiber]
    exact ⟨hyperplaneAnnToSocle eps φ g,hyperplane_ann_factor eps φ u0 hu0 g⟩
  · intro hv
    rw [mem_fixedFunctionalFiber] at hv
    obtain ⟨s,hs⟩ := hv
    have hann : s.1 ∈ Module.annihilator A (topHyperplane eps φ) := by
      rw [mem_annihilator_submodule_iff]
      intro x hx
      have h := congrArg (fun F => (F (topProjection eps x) : M)) hs
      change s.1 • x = φ (topProjection eps x) • v.1 at h
      rw [h,(mem_topHyperplane eps φ x).mp hx,zero_smul]
    refine ⟨⟨s.1,hann⟩,?_⟩
    change socleAction eps s u0 = v
    rw [hs]
    change φ u0 • v=v
    rw [hu0,one_smul]

def hyperplaneAnnFiberEquiv [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) (hφ : φ ≠ 0) :
    Module.annihilator A (topHyperplane eps φ) ≃ₗ[K]
      fixedFunctionalFiber (socleTensor eps) φ := by
  classical
  let u0 := Classical.choose (LinearMap.surjective hφ (1 : K))
  have hu0 : φ u0=1 := Classical.choose_spec (LinearMap.surjective hφ (1 : K))
  let f := hyperplaneAnnEval eps φ u0
  let f' : Module.annihilator A (topHyperplane eps φ) →ₗ[K]
      fixedFunctionalFiber (socleTensor eps) φ := f.codRestrict _ (fun g => by
    rw [← range_hyperplaneAnnEval eps φ u0 hu0]
    exact ⟨g,rfl⟩)
  apply LinearEquiv.ofBijective f'
  constructor
  · intro g h hgh
    exact hyperplaneAnnEval_injective eps φ u0 hu0 (congrArg Subtype.val hgh)
  · intro v
    have hv : v.1 ∈ LinearMap.range f := by
      rw [range_hyperplaneAnnEval eps φ u0 hu0]
      exact v.2
    obtain ⟨g,hg⟩ := hv
    exact ⟨g,Subtype.ext hg⟩

def lineQuotientAnnFunctional [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) (ψ : Module.Dual K (moduleSocle (M := M) eps)) :
    Module.annihilator A (M ⧸ socleLine eps v) →ₗ[K] Module.Dual K (Top (M := M) eps) where
  toFun g := ψ.comp (socleAction eps (lineQuotientAnnToSocle eps v g))
  map_add' := by
    intro g h
    ext q
    change ψ (socleAction eps
      (lineQuotientAnnToSocle eps v g+lineQuotientAnnToSocle eps v h) q) = _
    rw [map_add,LinearMap.add_apply,map_add]
    rfl
  map_smul' := by
    intro c g
    ext q
    change ψ (socleAction eps (c • lineQuotientAnnToSocle eps v g) q) = _
    rw [map_smul,LinearMap.smul_apply,map_smul]
    rfl

theorem line_quotient_ann_factor [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) (ψ : Module.Dual K (moduleSocle (M := M) eps))
    (hψ : ψ v=1) (g : Module.annihilator A (M ⧸ socleLine eps v)) :
    socleAction eps (lineQuotientAnnToSocle eps v g) =
      (lineQuotientAnnFunctional eps v ψ g).smulRight v :=
  eq_smulRight_of_range_line _ v ψ hψ (line_quotient_ann_action_range eps v g)

theorem lineQuotientAnnFunctional_injective [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) (ψ : Module.Dual K (moduleSocle (M := M) eps))
    (hψ : ψ v=1) : Function.Injective (lineQuotientAnnFunctional eps v ψ) := by
  intro g h hgh
  have hs := socleAction_injective (M := M) eps (show
      socleAction eps (lineQuotientAnnToSocle eps v g) =
        socleAction eps (lineQuotientAnnToSocle eps v h) by
    rw [line_quotient_ann_factor eps v ψ hψ g,line_quotient_ann_factor eps v ψ hψ h,hgh])
  exact Subtype.ext (congrArg (fun s : algebraSocle eps => (s : A)) hs)

theorem range_lineQuotientAnnFunctional [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) (ψ : Module.Dual K (moduleSocle (M := M) eps))
    (hψ : ψ v=1) : LinearMap.range (lineQuotientAnnFunctional eps v ψ) =
      fixedVectorFiber (socleTensor eps) v := by
  ext φ
  constructor
  · rintro ⟨g,rfl⟩
    rw [mem_fixedVectorFiber]
    exact ⟨lineQuotientAnnToSocle eps v g,line_quotient_ann_factor eps v ψ hψ g⟩
  · intro hφ
    rw [mem_fixedVectorFiber] at hφ
    obtain ⟨s,hs⟩ := hφ
    have hann : s.1 ∈ Module.annihilator A (M ⧸ socleLine eps v) := by
      rw [mem_annihilator_quotient_iff]
      intro x
      refine ⟨φ (topProjection eps x),?_⟩
      have h := congrArg (fun F => (F (topProjection eps x) : M)) hs
      exact h.symm
    refine ⟨⟨s.1,hann⟩,?_⟩
    apply LinearMap.ext
    intro q
    change ψ (socleAction eps s q) = φ q
    rw [hs]
    change ψ (φ q • v) = φ q
    rw [map_smul,hψ,smul_eq_mul,mul_one]

def lineQuotientAnnFiberEquiv [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) (hv : v ≠ 0) :
    Module.annihilator A (M ⧸ socleLine eps v) ≃ₗ[K]
      fixedVectorFiber (socleTensor eps) v := by
  classical
  let ψ := Classical.choose (Module.Projective.exists_dual_eq_one K hv)
  have hψ : ψ v=1 := Classical.choose_spec (Module.Projective.exists_dual_eq_one K hv)
  let f := lineQuotientAnnFunctional eps v ψ
  let f' : Module.annihilator A (M ⧸ socleLine eps v) →ₗ[K]
      fixedVectorFiber (socleTensor eps) v := f.codRestrict _ (fun g => by
    rw [← range_lineQuotientAnnFunctional eps v ψ hψ]
    exact ⟨g,rfl⟩)
  apply LinearEquiv.ofBijective f'
  constructor
  · intro g h hgh
    exact lineQuotientAnnFunctional_injective eps v ψ hψ (congrArg Subtype.val hgh)
  · intro φ
    have hφ : φ.1 ∈ LinearMap.range f := by
      rw [range_lineQuotientAnnFunctional eps v ψ hψ]
      exact φ.2
    obtain ⟨g,hg⟩ := hφ
    exact ⟨g,Subtype.ext hg⟩

theorem topHyperplane_restrictScalars_eq_kernel (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) :
    (topHyperplane eps φ).restrictScalars K = LinearMap.ker (φ.comp (topProjection eps)) := by
  ext x
  rfl

theorem socleLine_restrictScalars_eq_span (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) :
    (socleLine eps v).restrictScalars K = Submodule.span K ({v.1} : Set M) := by
  ext x
  change (∃ c : K, c • v.1=x) ↔ x ∈ Submodule.span K ({v.1} : Set M)
  exact Submodule.mem_span_singleton.symm

theorem topHyperplane_finrank_add_one [FiniteDimensional K M] (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) (hφ : φ ≠ 0) :
    finrank K (topHyperplane eps φ)+1 = finrank K M := by
  have hneq : φ.comp (topProjection eps) ≠ 0 := by
    intro hzero
    apply hφ
    apply LinearMap.ext
    intro q
    obtain ⟨x,rfl⟩ := topProjection_surjective eps q
    exact LinearMap.congr_fun hzero x
  change finrank K ((topHyperplane eps φ).restrictScalars K)+1 = finrank K M
  rw [topHyperplane_restrictScalars_eq_kernel]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero hneq

theorem socleLine_finrank_eq_one [FiniteDimensional K M] (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) (hv : v ≠ 0) : finrank K (socleLine eps v)=1 := by
  have hvM : v.1 ≠ 0 := fun h => hv (Subtype.ext h)
  change finrank K ((socleLine eps v).restrictScalars K)=1
  rw [socleLine_restrictScalars_eq_span]
  exact finrank_span_singleton hvM

theorem socleLine_quotient_finrank_add_one [FiniteDimensional K M] (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) (hv : v ≠ 0) :
    finrank K (M ⧸ socleLine eps v)+1 = finrank K M := by
  have hd := ((socleLine eps v).restrictScalars K).finrank_quotient_add_finrank
  change finrank K (M ⧸ socleLine eps v)+finrank K (socleLine eps v) = finrank K M at hd
  rw [socleLine_finrank_eq_one eps v hv] at hd
  exact hd

theorem socleTensor_finrank [FiniteDimensional K A] [FaithfulSMul A M]
    (eps : A →ₐ[K] K) : finrank K (socleTensor (M := M) eps) = finrank K (algebraSocle eps) :=
  LinearMap.finrank_range_of_inj (socleAction_injective (M := M) eps)

end Gerstenhaber.FourBlocks.MinimalSource
