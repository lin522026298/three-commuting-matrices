module

public import GKGraphDimension

@[expose] public section

noncomputable section
namespace GKGraph
variable (k : Type*) [Field k] (r : ℕ)
variable {F : Type*} [Field F] [Algebra k F]
def freeEval (T : Fin 3 → Mat F r) : Poly k r →ₐ[k] F :=
  MvPolynomial.aeval (fun z : FreeVars r => T z.1 z.2.1 z.2.2)

theorem freeEval_base (T : Fin 3 → Mat F r) (b : Fin 3) :
    (freeEval k r T).mapMatrix (base k r b) = T b := by
  ext i j
  exact MvPolynomial.aeval_X _ _

theorem freeEval_delta (T : Fin 3 → Mat F r) :
    freeEval k r T (delta k r) = (T 0).det := by
  rw [delta, AlgHom.map_det, freeEval_base]

def specOpen (T : Fin 3 → Mat F r) (h : IsUnit (T 0).det) : openRing k r →ₐ[k] F :=
  IsLocalization.Away.liftAlgHom (delta k r) (f := freeEval k r T)
    ((freeEval_delta k r T).symm ▸ h)

def specField (T : Fin 3 → Mat F r) (h : IsUnit (T 0).det) : ring k r →ₐ[k] F :=
  (specOpen k r T h).comp (toOpen k r)

theorem specField_poly (T : Fin 3 → Mat F r) (h : IsUnit (T 0).det) (x : Poly k r) :
    specField k r T h (fromPoly k r x) = freeEval k r T x := by
  change specOpen k r T h (toOpen k r (fromPoly k r x)) = _
  rw [toOpen_fromPoly]
  exact IsLocalization.Away.lift_eq (delta k r) ((freeEval_delta k r T).symm ▸ h) x

theorem specField_first (T : Fin 3 → Mat F r) (h : IsUnit (T 0).det) (b : Fin 3) :
    (specField k r T h).mapMatrix (gmat k r (b.castLE (by decide))) = T b := by
  ext i j
  have e := specField_poly k r T h (MvPolynomial.X (b,i,j))
  simpa [fromPoly, freeEval, gmat, AlgHom.mapMatrix_apply,Matrix.map_apply] using e

section IntegralPoint
variable {R : Type*} [CommRing R] [IsDomain R] [Algebra k R]
def pointBase (T : Fin 6 → Mat R r) : Fin 3 → Mat (FractionRing R) r :=
  fun b => (algebraMap R (FractionRing R)).mapMatrix (T (b.castLE (by decide)))

theorem pointUnit (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0) :
    IsUnit ((pointBase r T) 0).det := by
  change IsUnit (((algebraMap R (FractionRing R)).mapMatrix (T 0)).det)
  rw [← RingHom.map_det,isUnit_iff_ne_zero]
  exact (IsFractionRing.to_map_eq_zero_iff.not).2 hP

/-- Polynomial intertwining witnesses of well-definedness and commutation on a presented quotient. -/
structure Relations (T : Fin 6 → Mat R r) : Prop where
  y : T 0 * T 3 = T 1 * T 0
  z : T 0 * T 4 = T 2 * T 0
  comm : T 0 * T 5 = T 1 * T 2 - T 2 * T 1

def pointField (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0) : ring k r →ₐ[k] FractionRing R :=
  specField k r (pointBase r T) (pointUnit r T hP)

theorem point_value (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0)
    (hT : Relations r T) (i : Fin 6) :
    (pointField k r T hP).mapMatrix (gmat k r i) =
      (algebraMap R (FractionRing R)).mapMatrix (T i) := by
  let φ : Mat (ring k r) r →ₐ[k] Mat (FractionRing R) r := (pointField k r T hP).mapMatrix
  let α : Mat R r →+* Mat (FractionRing R) r := (algebraMap R (FractionRing R)).mapMatrix
  have e0 : φ (gmat k r 0) = α (T 0) := specField_first k r _ _ 0
  have e1 : φ (gmat k r 1) = α (T 1) := specField_first k r _ _ 1
  have e2 : φ (gmat k r 2) = α (T 2) := specField_first k r _ _ 2
  have cancel {a b : Mat (FractionRing R) r} (hh : α (T 0) * a = α (T 0) * b) : a=b := by
    have p := congrArg (fun v => (α (T 0))⁻¹ * v) hh
    have hu : IsUnit (α (T 0)).det := pointUnit r T hP
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul] using p
  change φ (gmat k r i) = α (T i)
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · change φ (gmat k r 3) = α (T 3)
    apply cancel
    calc _ = φ (gmat k r 0 * gmat k r 3) := by rw [map_mul,e0]
         _ = _ := by rw [ring_Y, map_mul,e1,e0,← map_mul,←hT.y,map_mul]
  · change φ (gmat k r 4) = α (T 4)
    apply cancel
    calc _ = φ (gmat k r 0 * gmat k r 4) := by rw [map_mul,e0]
         _ = _ := by rw [ring_Z, map_mul,e2,e0,← map_mul,←hT.z,map_mul]
  · change φ (gmat k r 5) = α (T 5)
    apply cancel
    calc _ = φ (gmat k r 0 * gmat k r 5) := by rw [map_mul,e0]
         _ = _ := by rw [← ring_comm_left,map_sub,map_mul,map_mul,e1,e2,←map_mul,←map_mul,
                       ←map_sub,←hT.comm,map_mul]

end IntegralPoint
end GKGraph
