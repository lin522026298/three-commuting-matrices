module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.FinCases

@[expose] public section

noncomputable section
namespace GKGraph
open Matrix
variable (k : Type*) [Field k] (r : ℕ)
abbrev FreeVars (r : ℕ) := Fin 3 × Fin r × Fin r
abbrev AllVars (r : ℕ) := Fin 6 × Fin r × Fin r
abbrev Poly := MvPolynomial (FreeVars r) k
abbrev K := FractionRing (Poly k r)
abbrev Mat (R : Type*) (r : ℕ) := Matrix (Fin r) (Fin r) R

def base (i : Fin 3) : Mat (Poly k r) r :=
  fun a b => MvPolynomial.X (i,a,b)

def delta : Poly k r := (base k r 0).det

theorem delta_ne_zero : delta k r ≠ 0 := by
  let ev := MvPolynomial.eval (R := k) (fun z : FreeVars r => (1 : Mat k r) z.2.1 z.2.2)
  have he : ev.mapMatrix (base k r 0) = 1 := by
    ext i j
    simp [ev, base, RingHom.mapMatrix_apply, Matrix.map_apply]
  intro hz
  have h := ev.map_det (base k r 0)
  rw [← delta, hz, map_zero, he, det_one] at h
  exact zero_ne_one h

def generic (i : Fin 3) : Mat (K k r) r :=
  (algebraMap (Poly k r) (K k r)).mapMatrix (base k r i)
abbrev P := generic k r 0
abbrev Y := generic k r 1
abbrev Z := generic k r 2
def comm (a b : Mat (K k r) r) := a*b-b*a
def rightY := (P k r)⁻¹ * Y k r * P k r
def rightZ := (P k r)⁻¹ * Z k r * P k r
def defect := (P k r)⁻¹ * (comm k r (Y k r) (Z k r))

theorem p_isUnit : IsUnit (P k r).det := by
  change IsUnit (((algebraMap (Poly k r) (K k r)).mapMatrix (base k r 0)).det)
  rw [← RingHom.map_det, isUnit_iff_ne_zero]
  exact fun h => delta_ne_zero k r ((IsFractionRing.to_map_eq_zero_iff).mp h)

theorem graph_intertwine_Y : P k r * rightY k r = Y k r * P k r := by
  simp only [rightY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (p_isUnit k r), one_mul]
theorem graph_intertwine_Z : P k r * rightZ k r = Z k r * P k r := by
  simp only [rightZ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (p_isUnit k r), one_mul]
theorem graph_comm_left : comm k r (Y k r) (Z k r) = P k r * defect k r := by
  simp only [defect, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (p_isUnit k r), one_mul]
theorem graph_comm_right : comm k r (rightY k r) (rightZ k r) = defect k r * P k r := by
  simp only [comm, rightY, rightZ, defect, mul_sub, sub_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ (p_isUnit k r)]

def six : Fin 6 → Mat (K k r) r :=
  ![P k r, Y k r, Z k r, rightY k r, rightZ k r, defect k r]
def coord (x : AllVars r) : K k r := six k r x.1 x.2.1 x.2.2
def ring : Subalgebra k (K k r) := Algebra.adjoin k (Set.range (coord k r))

theorem coord_mem (x : AllVars r) : coord k r x ∈ ring k r :=
  Algebra.subset_adjoin (Set.mem_range_self _)

def gcoord (x : AllVars r) : ring k r := ⟨coord k r x, coord_mem k r x⟩
def gmat (i : Fin 6) : Mat (ring k r) r := fun a b => gcoord k r (i,a,b)

theorem coe_gmat (i : Fin 6) : (ring k r).val.mapMatrix (gmat k r i) = six k r i := rfl

theorem generators : Algebra.adjoin k (Set.range (gcoord k r)) = ⊤ := by
  apply Subalgebra.map_injective (f := (ring k r).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, ← Set.range_comp, Algebra.map_top]
  exact (Subalgebra.range_val _).symm

instance : Algebra.FiniteType k (ring k r) := by
  classical
  exact ⟨⟨Finset.univ.image (gcoord k r), by simpa using generators k r⟩⟩

end GKGraph
