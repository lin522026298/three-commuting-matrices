module

public import ConcretePole
public import GKGraphMinor

@[expose] public section

noncomputable section
namespace GKDivisor
universe u
open IsDiscreteValuationRing
attribute [local instance] BadPole.cr BadPole.dom BadPole.dvr BadPole.alg

theorem strict_pole_of_real_minor (k : Type u) [Field k] [CharZero k] (r : ℕ)
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra k O]
    (T : Fin 6 → GKGraph.Mat O r) (ht : (T 0).det ≠ 0) (hT : GKGraph.Relations r T)
    (s : GKGraph.selectCols r)
    (hs : addVal O (GKGraph.fullMinor r (T 0) (T 1) (T 2) s) < addVal O ((T 0).det^(r-1))) :
    Nonempty (BadPole k r (GKGraph.universalMinor k r s)) := by
  obtain ⟨w,hw⟩ := addVal_le_iff_dvd.mp hs.le
  have hn : ¬ IsUnit w := by
    intro hu
    rw [hw,AddValuation.map_mul,addVal_eq_zero_iff.mpr hu,add_zero] at hs
    exact lt_irrefl _ hs
  have hz : GKGraph.fullMinor r (T 0) (T 1) (T 2) s ≠ 0 := by
    intro e; rw [e,AddValuation.map_zero] at hs; exact not_top_lt hs
  exact trueGraph_concrete_pole k r T ht hT (GKGraph.universalMinor k r s)
    (by rw [GKGraph.point_minor]; exact hz) w (by rw [GKGraph.point_minor,mul_comm]; exact hw.symm) hn

lemma strict_value_of_nonunit_mul {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (w a b : O) (hn : ¬IsUnit w) (hb : b ≠ 0) (he : w*a=b) : addVal O a < addVal O b := by
  apply lt_of_le_of_ne
  · exact addVal_le_iff_dvd.mpr ⟨w,by rw [← he,mul_comm]⟩
  · intro e
    obtain ⟨d,hd⟩ := addVal_le_iff_dvd.mp e.ge
    have he' : b * (w*d) = b * 1 := by
      calc _ = w * (b*d) := by ring
           _ = b * 1 := by rw [←hd,he,mul_one]
    exact hn (isUnit_iff_exists_inv.mpr ⟨d,mul_left_cancel₀ hb he'⟩)

namespace BadPole
variable {k : Type u} [Field k] {r : ℕ} {s : GKGraph.selectCols r}
variable (B : BadPole k r (GKGraph.universalMinor k r s))

def matrices : Fin 6 → GKGraph.Mat B.V r := fun i => B.f.mapMatrix (GKGraph.gmat k r i)

theorem det_ne_zero : (B.matrices 0).det ≠ 0 := by
  rw [matrices,←AlgHom.map_det,GKGraph.det_gmat]
  exact (map_ne_zero_iff _ B.inj).mpr (GKGraph.gdelta_ne_zero k r)

theorem matrix_relations : GKGraph.Relations r B.matrices := by
  refine ⟨?_,?_,?_⟩
  · exact (map_mul ..).symm.trans ((congrArg B.f.mapMatrix (GKGraph.ring_Y k r)).trans (map_mul ..))
  · exact (map_mul ..).symm.trans ((congrArg B.f.mapMatrix (GKGraph.ring_Z k r)).trans (map_mul ..))
  · simpa only [matrices,map_sub,map_mul] using congrArg B.f.mapMatrix (GKGraph.ring_comm_left k r).symm

theorem same_minor_strict :
    addVal B.V (GKGraph.fullMinor r (B.matrices 0) (B.matrices 1) (B.matrices 2) s) <
      addVal B.V ((B.matrices 0).det^(r-1)) := by
  have e := B.equation
  have hh : B.f (GKGraph.universalMinor k r s) =
      GKGraph.fullMinor r (B.matrices 0) (B.matrices 1) (B.matrices 2) s :=
    GKGraph.fullMinor_map r B.f.toRingHom _ _ _ _
  have hd : B.f (GKGraph.gdelta k r) = (B.matrices 0).det := by
    rw [←GKGraph.det_gmat,AlgHom.map_det]; rfl
  rw [hh,hd] at e
  exact strict_value_of_nonunit_mul B.w _ _ B.nonunit (pow_ne_zero _ B.det_ne_zero) e

end BadPole
#print axioms GKDivisor.strict_pole_of_real_minor
#print axioms GKDivisor.BadPole.same_minor_strict
end GKDivisor
