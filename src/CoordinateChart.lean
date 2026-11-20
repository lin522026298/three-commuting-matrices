module

public import RationalGauge
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

@[expose] public section

noncomputable section
namespace GKGauge
open LinearMap Module
universe u
variable {F : Type u} [Field F] {ι : Type u} [Fintype ι]
variable {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- Choose actual ambient coordinates on any finite-dimensional subspace or
injectively presented linear space, so evaluating just those coordinates is an
isomorphism. The selected coordinates have no repetitions. -/
theorem exists_chart (L : ι → V →ₗ[F] F) (hL : ∀ v ≠ (0 : V), ∃ i, L i v ≠ 0) :
    ∃ a : Fin (finrank F V) → ι, Function.Injective a ∧
      ∃ e : V ≃ₗ[F] (Fin (finrank F V) → F), ∀ v i, e v i = L (a i) v := by
  classical
  have hsp : Submodule.span F (Set.range L) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro v hv
    obtain ⟨i,hi⟩ := hL v hv
    exact ⟨_, ⟨i,rfl⟩, hi⟩
  obtain ⟨κ,a,ha,hsp',hli⟩ := exists_linearIndependent' F L
  let _ : Fintype κ := Fintype.ofInjective _ ha
  let b : Basis κ F (Module.Dual F V) := Basis.mk hli (by rw [hsp',hsp])
  have hcard : Fintype.card κ = finrank F V := by
    rw [← Module.finrank_eq_card_basis b, Subspace.dual_finrank_eq]
  let a' := (Fintype.equivFinOfCardEq hcard).symm
  let h := a' |>.trans (Equiv.refl κ)
  let b' := b.reindex h.symm
  let e := (Module.evalEquiv F V).trans (b'.constr F).symm
  refine ⟨a ∘ h, ha.comp h.injective, e, ?_⟩
  intro v i
  change ((b'.constr F).symm (Module.evalEquiv F V v)) i = _
  rw [Basis.constr_symm_apply]
  simp [b',b,Function.comp_def]

end GKGauge
#print axioms GKGauge.exists_chart
