module

public import Gerstenhaber.FourBlocks.MinimalSource.Pencil
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.Tactic.Linarith

/-!
The two-fiber dimension bound as finite linear algebra.  The quotient of
the full Hom space by the actual subspace T supplies the bilinear map;
there is no assumed annihilator pairing or assumed dimension estimate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap

variable {K U V : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]

/-- The actual rank-one operator v times a functional. -/
def rankOne : V →ₗ[K] Module.Dual K U →ₗ[K] (U →ₗ[K] V) where
  toFun v :=
    { toFun := fun φ => φ.smulRight v
      map_add' := by intros; ext; simp [add_smul]
      map_smul' := by intros; ext; simp [smul_smul] }
  map_add' := by intros; ext; simp [smul_add]
  map_smul' := by intros; ext; simp [smul_smul,mul_comm]

@[simp] theorem rankOne_apply (v : V) (φ : Module.Dual K U) (u : U) :
    rankOne v φ u = φ u • v := rfl

def quotientRankOne (T : Submodule K (U →ₗ[K] V)) :
    V →ₗ[K] Module.Dual K U →ₗ[K] ((U →ₗ[K] V) ⧸ T) where
  toFun v := T.mkQ.comp (rankOne v)
  map_add' := by intro v w; ext φ; simp [map_add]
  map_smul' := by intro a v; ext φ; simp [map_smul]

@[simp] theorem quotientRankOne_apply (T : Submodule K (U →ₗ[K] V))
    (v : V) (φ : Module.Dual K U) :
    quotientRankOne T v φ = T.mkQ (φ.smulRight v) := rfl

/-- The fiber with the functional fixed, parameterized by its actual
vector values rather than by an abstract tensor-space isomorphism. -/
def fixedFunctionalFiber (T : Submodule K (U →ₗ[K] V)) (φ : Module.Dual K U) :
    Submodule K V := LinearMap.ker ((quotientRankOne T).flip φ)

/-- The fiber with the output line fixed. -/
def fixedVectorFiber (T : Submodule K (U →ₗ[K] V)) (v : V) :
    Submodule K (Module.Dual K U) := LinearMap.ker (quotientRankOne T v)

@[simp] theorem mem_fixedFunctionalFiber (T : Submodule K (U →ₗ[K] V))
    (φ : Module.Dual K U) (v : V) :
    v ∈ fixedFunctionalFiber T φ ↔ φ.smulRight v ∈ T := by
  simp [fixedFunctionalFiber,LinearMap.mem_ker,Submodule.Quotient.mk_eq_zero]

@[simp] theorem mem_fixedVectorFiber (T : Submodule K (U →ₗ[K] V))
    (v : V) (φ : Module.Dual K U) :
    φ ∈ fixedVectorFiber T v ↔ φ.smulRight v ∈ T := by
  simp [fixedVectorFiber,LinearMap.mem_ker,Submodule.Quotient.mk_eq_zero]

@[simp] theorem fixedFunctionalFiber_zero (T : Submodule K (U →ₗ[K] V)) :
    fixedFunctionalFiber T 0 = ⊤ := by
  ext v
  simp

@[simp] theorem fixedVectorFiber_zero (T : Submodule K (U →ₗ[K] V)) :
    fixedVectorFiber T 0 = ⊤ := by
  ext φ
  simp

theorem quotientRankOne_spans [FiniteDimensional K U]
    (T : Submodule K (U →ₗ[K] V)) :
    Submodule.span K (Set.range (fun p : V × Module.Dual K U =>
      quotientRankOne T p.1 p.2)) = ⊤ := by
  classical
  apply top_unique
  intro z _
  obtain ⟨f,rfl⟩ := T.mkQ_surjective z
  let b := Module.finBasis K U
  have hf : f = ∑ i, (b.coord i).smulRight (f (b i)) := by
    ext u
    rw [LinearMap.sum_apply]
    change f u = ∑ i, b.coord i u • f (b i)
    simpa only [map_sum,map_smul,Basis.coord_apply] using
      (congrArg f (b.sum_repr u)).symm
  rw [hf,map_sum]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.subset_span ⟨(f (b i),b.coord i),rfl⟩

theorem quotient_finrank_le_product_of_fibers [Infinite K]
    [FiniteDimensional K U] [FiniteDimensional K V]
    (T : Submodule K (U →ₗ[K] V)) (c : ℕ)
    (hfunctional : ∀ φ : Module.Dual K U, c ≤ finrank K (fixedFunctionalFiber T φ))
    (hvector : ∀ v : V, c ≤ finrank K (fixedVectorFiber T v)) :
    finrank K ((U →ₗ[K] V) ⧸ T) ≤ (finrank K U-c)*(finrank K V-c) := by
  apply bilinear_slice_finrank_le_product (quotientRankOne T)
    (finrank K U-c) (finrank K V-c) (quotientRankOne_spans T)
  · intro v
    have hrank := (quotientRankOne T v).finrank_range_add_finrank_ker
    rw [Subspace.dual_finrank_eq] at hrank
    have hk := hvector v
    change c ≤ finrank K (LinearMap.ker (quotientRankOne T v)) at hk
    omega
  · intro φ
    have hrank := ((quotientRankOne T).flip φ).finrank_range_add_finrank_ker
    have hk := hfunctional φ
    change c ≤ finrank K (LinearMap.ker ((quotientRankOne T).flip φ)) at hk
    omega

private theorem nat_two_fiber_arithmetic (a b c d q : ℕ)
    (hca : c ≤ a) (hcb : c ≤ b) (hd : q+d=a*b)
    (hq : q ≤ (a-c)*(b-c)) : c*(a+b-c) ≤ d := by
  obtain ⟨a',ha⟩ := Nat.exists_eq_add_of_le hca
  obtain ⟨b',hb⟩ := Nat.exists_eq_add_of_le hcb
  rw [ha,hb] at hd hq ⊢
  simp only [Nat.add_sub_cancel_left] at hq
  have hs : c+a'+(c+b')-c = c+a'+b' := by omega
  rw [hs]
  nlinarith

/-- General two-fiber socle-tensor budget.  The numerical estimate is
derived from the literal quotient and its two kernel families. -/
theorem socle_tensor_finrank_budget [Infinite K]
    [FiniteDimensional K U] [FiniteDimensional K V]
    (T : Submodule K (U →ₗ[K] V)) (c : ℕ)
    (hfunctional : ∀ φ : Module.Dual K U, c ≤ finrank K (fixedFunctionalFiber T φ))
    (hvector : ∀ v : V, c ≤ finrank K (fixedVectorFiber T v)) :
    c*(finrank K U+finrank K V-c) ≤ finrank K T := by
  have hca : c ≤ finrank K U := by
    have h := (hvector (0 : V)).trans (Submodule.finrank_le _)
    simpa only [Subspace.dual_finrank_eq] using h
  have hcb : c ≤ finrank K V :=
    (hfunctional (0 : Module.Dual K U)).trans (Submodule.finrank_le _)
  have hd := T.finrank_quotient_add_finrank
  rw [Module.finrank_linearMap] at hd
  exact nat_two_fiber_arithmetic _ _ c _ _ hca hcb hd
    (quotient_finrank_le_product_of_fibers T c hfunctional hvector)

/-- The c=2 bound used by the finite four-block minimum argument. -/
theorem socle_tensor_two_fiber_budget [Infinite K]
    [FiniteDimensional K U] [FiniteDimensional K V]
    (T : Submodule K (U →ₗ[K] V))
    (hfunctional : ∀ φ : Module.Dual K U, 2 ≤ finrank K (fixedFunctionalFiber T φ))
    (hvector : ∀ v : V, 2 ≤ finrank K (fixedVectorFiber T v)) :
    2*(finrank K U+finrank K V-2) ≤ finrank K T :=
  socle_tensor_finrank_budget T 2 hfunctional hvector

/-- Nonzero-fiber form, matching the two actual annihilator families.
The bounds c<=dim U and c<=dim V are consequences, not hypotheses. -/
theorem socle_tensor_nonzero_fiber_budget [Infinite K]
    [FiniteDimensional K U] [FiniteDimensional K V] [Nontrivial U] [Nontrivial V]
    (T : Submodule K (U →ₗ[K] V)) (c : ℕ)
    (hfunctional : ∀ φ : Module.Dual K U, φ ≠ 0 →
      c ≤ finrank K (fixedFunctionalFiber T φ))
    (hvector : ∀ v : V, v ≠ 0 → c ≤ finrank K (fixedVectorFiber T v)) :
    c ≤ finrank K U ∧ c ≤ finrank K V ∧
      c*(finrank K U+finrank K V-c) ≤ finrank K T := by
  classical
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  obtain ⟨φ,hφ⟩ := exists_ne (0 : Module.Dual K U)
  have hca : c ≤ finrank K U := by
    simpa only [Subspace.dual_finrank_eq] using
      (hvector v hv).trans (Submodule.finrank_le _)
  have hcb : c ≤ finrank K V :=
    (hfunctional φ hφ).trans (Submodule.finrank_le _)
  refine ⟨hca,hcb,socle_tensor_finrank_budget T c ?_ ?_⟩
  · intro ψ
    by_cases hψ : ψ = 0
    · subst ψ
      rw [fixedFunctionalFiber_zero,finrank_top]
      exact hcb
    · exact hfunctional ψ hψ
  · intro w
    by_cases hw : w = 0
    · subst w
      rw [fixedVectorFiber_zero,finrank_top,Subspace.dual_finrank_eq]
      exact hca
    · exact hvector w hw

/-- A strict type deficit supplies an actual fiber of dimension at most
one, on one side or the other. -/
theorem exists_small_fiber_of_finrank_lt [Infinite K]
    [FiniteDimensional K U] [FiniteDimensional K V] [Nontrivial U] [Nontrivial V]
    (T : Submodule K (U →ₗ[K] V))
    (hsmall : finrank K T < 2*(finrank K U+finrank K V-2)) :
    (∃ φ : Module.Dual K U, φ ≠ 0 ∧ finrank K (fixedFunctionalFiber T φ) ≤ 1) ∨
      (∃ v : V, v ≠ 0 ∧ finrank K (fixedVectorFiber T v) ≤ 1) := by
  classical
  by_cases hφ : ∃ φ : Module.Dual K U, φ ≠ 0 ∧
      finrank K (fixedFunctionalFiber T φ) ≤ 1
  · exact Or.inl hφ
  · right
    by_contra hv
    have hfunctional (φ : Module.Dual K U) (hφ0 : φ ≠ 0) :
        2 ≤ finrank K (fixedFunctionalFiber T φ) := by
      have hnot : ¬finrank K (fixedFunctionalFiber T φ) ≤ 1 :=
        fun h => hφ ⟨φ,hφ0,h⟩
      omega
    have hvector (v : V) (hv0 : v ≠ 0) : 2 ≤ finrank K (fixedVectorFiber T v) := by
      have hnot : ¬finrank K (fixedVectorFiber T v) ≤ 1 :=
        fun h => hv ⟨v,hv0,h⟩
      omega
    have hbudget := (socle_tensor_nonzero_fiber_budget T 2 hfunctional hvector).2.2
    omega

end Gerstenhaber.FourBlocks.MinimalSource
