import GKGraphSpecialize
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

noncomputable section
namespace GKGraph
variable (k : Type*) [Field k] (r : ℕ)
section Images
variable {A : Type*} [CommRing A] [Algebra k A]

theorem range_generated (φ : ring k r →ₐ[k] A) :
    φ.range = Algebra.adjoin k (Set.range (φ ∘ gcoord k r)) := by
  rw [← Algebra.map_top, ← generators k r, AlgHom.map_adjoin, Set.range_comp]

end Images
section Integral
variable {R : Type*} [CommRing R] [IsDomain R] [Algebra k R]
abbrev incl : R →ₐ[k] FractionRing R := IsScalarTower.toAlgHom k R (FractionRing R)

private theorem whole_range (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0)
    (hT : Relations r T) :
    (pointField k r T hP).range ≤ (incl k (R := R)).range := by
  rw [range_generated]
  apply Algebra.adjoin_le
  rintro _ ⟨i,rfl⟩
  exact ⟨T i.1 i.2.1 i.2.2, (congrFun (congrFun (point_value k r T hP hT i.1) i.2.1) i.2.2).symm⟩

/-- Integral specialization of the actual saturated graph. The map on the polynomial
variables need NOT be injective. The three integral divisions on the presented
module are witnesses, not an assumed map on the graph ring. -/
def point (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0) (hT : Relations r T) :
    ring k r →ₐ[k] R :=
  (AlgEquiv.ofInjective (incl k (R := R)) (IsFractionRing.injective _ _)).symm.toAlgHom.comp
    ((pointField k r T hP).codRestrict (incl k (R := R)).range
      (fun a => whole_range k r T hP hT ⟨a,rfl⟩))

theorem point_coe (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0) (hT : Relations r T)
    (a : ring k r) : incl k (point k r T hP hT a) = pointField k r T hP a := by
  let e := AlgEquiv.ofInjective (incl k (R := R)) (IsFractionRing.injective _ _)
  exact congrArg Subtype.val (e.apply_symm_apply ⟨_, whole_range k r T hP hT ⟨a,rfl⟩⟩)

theorem point_matrix (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0) (hT : Relations r T)
    (b : Fin 6) : (point k r T hP hT).mapMatrix (gmat k r b) = T b := by
  ext i j
  apply IsFractionRing.injective R (FractionRing R)
  change incl k (point k r T hP hT (gmat k r b i j)) = _
  rw [point_coe]
  exact congrFun (congrFun (point_value k r T hP hT b) i) j

theorem point_det (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0) (hT : Relations r T) :
    point k r T hP hT (gdelta k r) = (T 0).det := by
  rw [←det_gmat, AlgHom.map_det, point_matrix]

end Integral
end GKGraph
