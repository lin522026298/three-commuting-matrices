import NilOperator
import GroundLength
import DividedTail
noncomputable section
namespace DivisorG3
open Module PowerSeries LinearMap
variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
/-- We retain both the polynomial action equality and the action on each actual vector. -/
theorem original_action (T : End k W) (ht : IsNilpotent T) :
    ∃ ρ : O k →ₐ[k] End k W, ∃ _ : Module (O k) W, ∃ _ : IsScalarTower k (O k) W,
      ρ X=T ∧ ρ.range=Algebra.adjoin k ({T}:Set _) ∧
      (∀ s : O k, ∀ w : W, s • w=ρ s w) ∧
      (∃ a : O k, a≠0 ∧ ∀ w : W, a • w=0) ∧
      (∀ Y : End k W, Commute Y T → ∃ y : End (O k) W, y.restrictScalars k=Y) := by
  obtain ⟨ρ,hx,hr⟩ := series_of_nil T ht
  let _ : Module (O k) W := Module.compHom W ρ.toRingHom
  let _ : IsScalarTower k (O k) W := IsScalarTower.of_algebraMap_smul fun c w => by
    change ρ (algebraMap k (O k) c) w = c • w
    rw [ρ.commutes]; rfl
  refine ⟨ρ,inferInstance,inferInstance,hx,hr,fun _ _ => rfl,?_,?_⟩
  · obtain ⟨e,he⟩ := ht
    refine ⟨X^e,pow_ne_zero _ X_ne_zero,fun w => ?_⟩
    change ρ (X^e) w=0
    rw [map_pow,hx,he]; rfl
  · intro Y hY
    refine ⟨{ toFun:=Y
              map_add':=Y.map_add
              map_smul':=fun s w => ?_ },rfl⟩
    change Y (ρ s w) = ρ s (Y w)
    exact LinearMap.congr_fun (Algebra.commute_of_mem_adjoin_singleton_of_commute
      (show ρ s ∈ Algebra.adjoin k ({T}:Set _) from hr ▸ ⟨s,rfl⟩) hY).eq w
#print axioms original_action
end DivisorG3
