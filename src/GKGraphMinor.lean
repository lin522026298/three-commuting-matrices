import GKGraphInversePoint
import BlockIndex
import BoxWords
noncomputable section
namespace GKGraph
variable (k : Type*) [Field k] (r : ℕ)
abbrev Row (r : ℕ) := Fin r × Fin r
abbrev Col (r : ℕ) := Row r ⊕ Row r
abbrev selectCols (r : ℕ) := Row r → Col r
variable {A B : Type*} [CommRing A] [CommRing B]
def hMatrix (P Y Z : Mat A r) : Matrix (Row r) (Col r) A :=
  DivisorG3.blockColumns P (DivisorG3.box Y Z r r)
def fullMinor (P Y Z : Mat A r) (s : selectCols r) := ((hMatrix r P Y Z).submatrix id s).det

theorem hMatrix_map (f : A →+* B) (P Y Z : Mat A r) :
    (hMatrix r P Y Z).map f = hMatrix r (f.mapMatrix P) (f.mapMatrix Y) (f.mapMatrix Z) := by
  ext ⟨i,j⟩ a
  cases a with
  | inl a =>
    simp [hMatrix,DivisorG3.blockColumns,DivisorG3.diagP,Matrix.blockDiagonal_apply,
      Matrix.fromCols,Matrix.map_apply,apply_ite f,RingHom.mapMatrix_apply]
  | inr a =>
    change f.mapMatrix (Y^a.1.val*Z^a.2.val) i j = (f.mapMatrix Y^a.1.val*f.mapMatrix Z^a.2.val) i j
    simp only [map_mul,map_pow]

theorem fullMinor_map (f : A →+* B) (P Y Z : Mat A r) (s : selectCols r) :
    f (fullMinor r P Y Z s) = fullMinor r (f.mapMatrix P) (f.mapMatrix Y) (f.mapMatrix Z) s := by
  unfold fullMinor
  rw [RingHom.map_det]
  change (((hMatrix r P Y Z).map f).submatrix id s).det = _
  rw [hMatrix_map]

def universalMinor (s : selectCols r) : ring k r := fullMinor r (gmat k r 0) (gmat k r 1) (gmat k r 2) s

variable {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
variable (T : Fin 6 → Mat O r) (hp : (T 0).det ≠ 0) (ht : Relations r T)

theorem point_minor (s : selectCols r) :
    point k r T hp ht (universalMinor k r s) = fullMinor r (T 0) (T 1) (T 2) s := by
  change (point k r T hp ht).toRingHom (fullMinor r _ _ _ s) = _
  rw [fullMinor_map]
  change fullMinor r ((point k r T hp ht).mapMatrix _) ((point k r T hp ht).mapMatrix _)
    ((point k r T hp ht).mapMatrix _) s = _
  rw [point_matrix,point_matrix,point_matrix]

open IsDiscreteValuationRing
variable [IsDiscreteValuationRing O]
include hp ht in
theorem strict_minor_nonunit (s : selectCols r)
    (hs : addVal O (fullMinor r (T 0) (T 1) (T 2) s) < addVal O ((T 0).det^(r-1))) :
    let h := universalMinor k r s
    GKRational.q (K := K k r) (gdelta k r ^ (r-1)) h ≠ 0 ∧
      ¬ IsUnit (GKRational.q (K := K k r) (gdelta k r ^ (r-1)) h) := by
  obtain ⟨w,hw⟩ := addVal_le_iff_dvd.mp hs.le
  have hn : ¬ IsUnit w := by
    intro hu
    have h := hs
    rw [hw,AddValuation.map_mul,addVal_eq_zero_iff.mpr hu,add_zero] at h
    exact lt_irrefl _ h
  have hz : fullMinor r (T 0) (T 1) (T 2) s ≠ 0 := by intro e; rw [e,AddValuation.map_zero] at hs; exact not_top_lt hs
  have H := nonunit_inverse_point k r T hp ht (universalMinor k r s)
    (by rw [point_minor]; exact hz) w (by rw [point_minor,mul_comm]; exact hw.symm) hn
  obtain ⟨_,_,_,h1,h2⟩ := H
  exact ⟨h1,h2⟩

end GKGraph
