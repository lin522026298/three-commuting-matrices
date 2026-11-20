module

public import GKGraphMinor
public import GKRationalResidual
public import GKGraphCoordinates

@[expose] public section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
namespace GKGraph
universe u
variable (k : Type u) [Field k] (r : ℕ)
variable {F : Type u} [Field F] [Algebra k F]

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem residue_trdeg_eq_image (φ : ring k r →ₐ[k] F) :
    Algebra.trdeg k (residueCoordinates k r φ) = Algebra.trdeg k φ.range := by
  rw [range_generated]
  unfold residueCoordinates
  let S := Set.range (φ ∘ gcoord k r)
  have hi : Algebra.IsAlgebraic (Algebra.adjoin k S) (IntermediateField.adjoin k S) := inferInstance
  change Algebra.trdeg k (IntermediateField.adjoin k S) = _
  rw [← trdeg_add_eq k (Algebra.adjoin k S) (A := IntermediateField.adjoin k S),
      trdeg_eq_zero_iff.2 hi, add_zero]

variable {O : Type*} [CommRing O] [IsDomain O]
def datum (φ : ring k r →+* O) : Fin 6 → Mat O r := fun i => φ.mapMatrix (gmat k r i)

omit [IsDomain O] in
theorem datum_relations (φ : ring k r →+* O) : Relations r (datum k r φ) := by
  constructor
  · exact (map_mul _ _ _).symm.trans ((congrArg φ.mapMatrix (ring_Y k r)).trans (map_mul _ _ _))
  · exact (map_mul _ _ _).symm.trans ((congrArg φ.mapMatrix (ring_Z k r)).trans (map_mul _ _ _))
  · have h := congrArg φ.mapMatrix (ring_comm_left k r).symm
    simpa only [datum,map_mul,map_sub] using h

omit [IsDomain O] in
theorem datum_det (φ : ring k r →+* O) : ((datum k r φ) 0).det = φ (gdelta k r) := by
  rw [←det_gmat,RingHom.map_det]; rfl

omit [IsDomain O] in
theorem datum_minor (φ : ring k r →+* O) (s : selectCols r) :
    φ (universalMinor k r s) =
      fullMinor r (datum k r φ 0) (datum k r φ 1) (datum k r φ 2) s := fullMinor_map .. 

variable [IsDiscreteValuationRing O]
open IsDiscreteValuationRing

/-- If a genuine inverse-minor chart maps into a new DVR with nonunit adjoined
coordinate and nonzero determinant, the SAME column selection gives a strict
minor on its six actual matrices. No uniformizer or isomorphic old DVR is used. -/
theorem strict_at_inverse_pole (s : selectCols r)
    (ψ : GKRational.adj (K := K k r) (gdelta k r ^ (r-1)) (universalMinor k r s) →+* O)
    (φ : ring k r →+* O) (extends_ : ∀ b, ψ (algebraMap _ _ b) = φ b)
    (hδ : φ (gdelta k r) ≠ 0) (hd : universalMinor k r s ≠ 0)
    (hn : ¬ IsUnit (ψ (GKRational.q _ _))) :
    addVal O (fullMinor r (datum k r φ 0) (datum k r φ 1) (datum k r φ 2) s) <
      addVal O ((datum k r φ 0).det^(r-1)) := by
  rw [←datum_minor,datum_det]
  let b := universalMinor k r s
  let w := ψ (GKRational.q (K := K k r) (gdelta k r^(r-1)) b)
  have he : w * φ b = φ (gdelta k r)^(r-1) := by
    calc w * φ b = w * ψ (algebraMap _ _ b) := congrArg (w * ·) (extends_ b).symm
         _ = ψ (GKRational.q _ _ * algebraMap _ _ b) := (map_mul _ _ _).symm
         _ = ψ (algebraMap _ _ (gdelta k r^(r-1))) :=
           congrArg ψ (GKRational.qmul (K := K k r) (gdelta k r^(r-1)) b hd)
         _ = φ (gdelta k r^(r-1)) := extends_ _
         _ = _ := map_pow ..
  have hb : φ b ≠ 0 := fun e => (pow_ne_zero _ hδ) (by rw [←he,e,mul_zero])
  change addVal O (φ b) < _
  apply lt_of_le_not_ge
  · apply addVal_le_iff_dvd.mpr; exact ⟨w,he.symm.trans (mul_comm _ _)⟩
  · intro h
    obtain ⟨c,hc⟩ := addVal_le_iff_dvd.mp h
    have hw : w*c=1 := mul_left_cancel₀ hb (by
      calc φ b*(w*c) = (w*φ b)*c := by ac_rfl
           _ = φ b := he ▸ hc.symm
           _ = φ b*1 := (mul_one _).symm)
    exact hn (IsUnit.of_mul_eq_one _ hw)

end GKGraph
