module

public import GKGraphOpen

@[expose] public section
noncomputable section
namespace GKGraph
variable (k : Type*) [Field k] (r : ℕ)

theorem field_trdeg : Algebra.trdeg k (K k r) = (3*r*r : ℕ) := by
  have := IsLocalization.isAlgebraic (K k r) (nonZeroDivisors (Poly k r))
  rw [← trdeg_add_eq k (Poly k r) (A := K k r),
    trdeg_eq_zero_iff.2 this, add_zero, MvPolynomial.trdeg_of_isDomain]
  simp [FreeVars, mul_assoc]

theorem ring_trdeg : Algebra.trdeg k (ring k r) = (3*r*r : ℕ) := by
  have := IsLocalization.isAlgebraic (K k r) (nonZeroDivisors (ring k r))
  have h := trdeg_add_eq k (ring k r) (A := K k r)
  rw [trdeg_eq_zero_iff.2 this, add_zero, field_trdeg] at h
  exact h

private theorem mat_inj : Function.Injective (fun a : Mat (ring k r) r => (ring k r).val.mapMatrix a) := by
  intro a b h
  ext i j
  exact congrFun (congrFun h i) j

theorem ring_Y : gmat k r 0 * gmat k r 3 = gmat k r 1 * gmat k r 0 := by
  apply mat_inj k r
  simp only [map_mul, coe_gmat]
  exact graph_intertwine_Y k r

theorem ring_Z : gmat k r 0 * gmat k r 4 = gmat k r 2 * gmat k r 0 := by
  apply mat_inj k r
  simp only [map_mul, coe_gmat]
  exact graph_intertwine_Z k r

theorem ring_comm_left :
    gmat k r 1 * gmat k r 2 - gmat k r 2 * gmat k r 1 = gmat k r 0 * gmat k r 5 := by
  apply mat_inj k r
  simp only [map_sub, map_mul, coe_gmat]
  exact graph_comm_left k r

theorem ring_comm_right :
    gmat k r 3 * gmat k r 4 - gmat k r 4 * gmat k r 3 = gmat k r 5 * gmat k r 0 := by
  apply mat_inj k r
  simp only [map_sub, map_mul, coe_gmat]
  exact graph_comm_right k r

theorem det_gmat : (gmat k r 0).det = gdelta k r := by
  apply Subtype.ext
  change (ring k r).val ((gmat k r 0).det) = (fromPoly k r (delta k r) : K k r)
  rw [fromPoly_val, AlgHom.map_det,coe_gmat]
  exact ((algebraMap (Poly k r) (K k r)).map_det (base k r 0)).symm

end GKGraph
