import SquareCover
import GroundLength
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
noncomputable section
namespace DivisorG3
open Module Submodule IsLocalRing PowerSeries
variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
variable [Module (O k) W] [IsScalarTower k (O k) W]
theorem minimal_cover (T : End k W) (hx : ∀ w : W, (X : O k) • w=T w) :
    ∃ π : (Fin (finrank k (LinearMap.ker T)) → O k) →ₗ[O k] W, Function.Surjective π := by
  let N : Submodule (O k) W := maximalIdeal (O k) • ⊤
  have hr : N.restrictScalars k = T.range := by
    ext w
    simp only [N,PowerSeries.maximalIdeal_eq_span_X,Submodule.ideal_span_singleton_smul]
    change (∃ v ∈ (⊤ : Submodule (O k) W), (X : O k) • v=w) ↔ ∃ v, T v=w
    simp [hx]
  have dim : finrank k (W ⧸ N)=finrank k (LinearMap.ker T) := by
    rw [←(Submodule.Quotient.restrictScalarsEquiv k N).finrank_eq, hr]
    have h := T.finrank_range_add_finrank_ker
    have e := T.range.finrank_quotient_add_finrank
    omega
  let β := Module.finBasisOfFinrankEq k (W ⧸ N) dim
  choose b hb using fun i => N.mkQ_surjective (β i)
  have eqb : N.mkQ ∘ b = β := funext hb
  let _ : Module.Finite (O k) W := Module.Finite.of_restrictScalars_finite k _ _
  have spanb : span (O k) (Set.range b)=⊤ := by
    symm
    apply Submodule.eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson (I:=maximalIdeal (O k))
      Module.Finite.fg_top (ringJacobson_eq_maximalIdeal (O k)).ge
    change (⊤ : Submodule (O k) W).map N.mkQ = _
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr N.mkQ_surjective,Submodule.map_span,←Set.range_comp,eqb]
    symm; apply top_unique
    intro v _
    exact (Submodule.span_le_restrictScalars k (O k) (Set.range β)) (β.span_eq ▸ Submodule.mem_top)
  exact ⟨Fintype.linearCombination (O k) b,LinearMap.range_eq_top.mp ((Fintype.range_linearCombination _ _).trans spanb)⟩
#print axioms minimal_cover
end DivisorG3
