import GKGraphIntegral
import GKRationalAdjunction

noncomputable section
namespace GKGraph
variable (k : Type*) [Field k] (r : ℕ)
variable {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]

theorem gdelta_ne_zero : gdelta k r ≠ 0 := by
  intro h
  have hh := congrArg (fun x : ring k r => (x : K k r)) h
  change (fromPoly k r (delta k r) : K k r) = 0 at hh
  rw [fromPoly_val,IsFractionRing.to_map_eq_zero_iff] at hh
  exact delta_ne_zero k r hh

/-- A strict minor with actual integral nonunit quotient creates the nonzero nonunit in
the graph enlarged by the inverse-minor fraction. Its denominator is not inverted in O. -/
theorem nonunit_inverse_point (T : Fin 6 → Mat O r) (hP : (T 0).det ≠ 0) (hT : Relations r T)
    (h : ring k r) (B : point k r T hP hT h ≠ 0) (w : O)
    (hw : w * point k r T hP hT h = (T 0).det^(r-1)) (hn : ¬ IsUnit w) :
    ∃ f : GKRational.adj (K := K k r) ((gdelta k r)^(r-1)) h →+* O,
      (∀ x : ring k r, f (algebraMap _ _ x) = point k r T hP hT x) ∧
      f (GKRational.q _ _) = w ∧
      GKRational.q (K := K k r) ((gdelta k r)^(r-1)) h ≠ 0 ∧
      ¬ IsUnit (GKRational.q (K := K k r) ((gdelta k r)^(r-1)) h) := by
  let f := (point k r T hP hT).toRingHom
  let a := (gdelta k r)^(r-1)
  have ha : a ≠ 0 := pow_ne_zero _ (gdelta_ne_zero k r)
  have he : w * f h = f a := by simpa only [f, a, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_pow,point_det] using hw
  refine ⟨GKRational.specialize (K := K k r) f a h B w he,
    GKRational.spec_base _ _ _ _ _ _, GKRational.spec_q _ _ _ _ _ _, ?_, ?_⟩
  · exact GKRational.q_ne_zero _ _ ha (fun e => B (by rw [e,map_zero]))
  · exact GKRational.q_nonunit f a h B w he hn

end GKGraph
