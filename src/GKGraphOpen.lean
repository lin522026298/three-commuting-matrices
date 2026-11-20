module

public import GKGraphCore
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

noncomputable section
namespace GKGraph
open Matrix IsLocalization
variable (k : Type*) [Field k] (r : ℕ)

def fromPoly : Poly k r →ₐ[k] ring k r :=
  MvPolynomial.aeval (fun z : FreeVars r => gcoord k r (z.1.castLE (by decide),z.2))

theorem fromPoly_val (x : Poly k r) : (fromPoly k r x : K k r) = algebraMap _ _ x := by
  have e : (ring k r).val.comp (fromPoly k r) = IsScalarTower.toAlgHom k (Poly k r) (K k r) := by
    apply MvPolynomial.algHom_ext
    intro a
    obtain ⟨i,u,v⟩ := a
    fin_cases i <;> simp [fromPoly, gcoord, coord, six, generic, base, RingHom.mapMatrix_apply,
      Matrix.map_apply]
  exact DFunLike.congr_fun e x

instance graphFraction : IsFractionRing (ring k r) (K k r) := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨x,y,_,e⟩ := IsFractionRing.div_surjective (Poly k r) z
  exact ⟨fromPoly k r x, fromPoly k r y, by change z = (fromPoly k r x : K k r) / (fromPoly k r y : K k r); rw [fromPoly_val, fromPoly_val]; exact e.symm⟩

def gdelta := fromPoly k r (delta k r)
abbrev openRing := Localization.subalgebra.ofField (K k r) (Submonoid.powers (delta k r))
  (powers_le_nonZeroDivisors_of_noZeroDivisors (delta_ne_zero k r))

abbrev openBase (b : Fin 3) : Mat (openRing k r) r :=
  (algebraMap (Poly k r) (openRing k r)).mapMatrix (base k r b)

theorem openUnit : IsUnit (openBase k r 0).det := by
  rw [openBase, ← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (delta k r)

abbrev openVal := (openRing k r).val.toRingHom
theorem openBase_val (i : Fin 3) : (openVal k r).mapMatrix (openBase k r i) = generic k r i := rfl

theorem openInv_val : (openVal k r).mapMatrix (openBase k r 0)⁻¹ = (P k r)⁻¹ := by
  apply left_inv_eq_right_inv (a := P k r)
  · change _ * (openVal k r).mapMatrix (openBase k r 0) = 1
    rw [← map_mul, Matrix.nonsing_inv_mul _ (openUnit k r), map_one]
  · exact Matrix.mul_nonsing_inv _ (p_isUnit k r)

def openSix : Fin 6 → Mat (openRing k r) r :=
  let p := openBase k r 0
  let y := openBase k r 1
  let z := openBase k r 2
  ![p,y,z,p⁻¹*y*p,p⁻¹*z*p,p⁻¹*(y*z-z*y)]

theorem openSix_val (b : Fin 6) :
    (openVal k r).mapMatrix (openSix k r b) = six k r b := by
  fin_cases b
  · rfl
  · rfl
  · rfl
  · change (openVal k r).mapMatrix ((openBase k r 0)⁻¹ * openBase k r 1 * openBase k r 0) = _
    rw [map_mul, map_mul, openInv_val]; rfl
  · change (openVal k r).mapMatrix ((openBase k r 0)⁻¹ * openBase k r 2 * openBase k r 0) = _
    rw [map_mul, map_mul, openInv_val]; rfl
  · change (openVal k r).mapMatrix ((openBase k r 0)⁻¹ * _) = _
    rw [map_mul, openInv_val, map_sub, map_mul, map_mul]; rfl

theorem incl_open : ring k r ≤ (openRing k r).restrictScalars k := by
  apply Algebra.adjoin_le
  rintro x ⟨b,rfl⟩
  have e := congrFun (congrFun (openSix_val k r b.1) b.2.1) b.2.2
  change six k r b.1 b.2.1 b.2.2 ∈ openRing k r
  rw [← e]
  exact (openSix k r b.1 b.2.1 b.2.2).property

def toOpen : ring k r →ₐ[k] openRing k r := Subalgebra.inclusion (incl_open k r)

instance graphOpenAlg : Algebra (ring k r) (openRing k r) := (toOpen k r).toRingHom.toAlgebra

theorem toOpen_fromPoly (x : Poly k r) :
    toOpen k r (fromPoly k r x) = algebraMap _ (openRing k r) x :=
  Subtype.ext (fromPoly_val k r x)

theorem algebraMap_graphOpen (x : ring k r) :
    algebraMap _ (openRing k r) x = toOpen k r x := rfl

instance openGraph : IsLocalization.Away (gdelta k r) (openRing k r) := by
  apply IsLocalization.Away.mk
  · rw [algebraMap_graphOpen, gdelta, toOpen_fromPoly]
    exact IsLocalization.Away.algebraMap_isUnit _
  · intro s
    obtain ⟨n,a,h⟩ := IsLocalization.Away.surj (delta k r) s
    exact ⟨n, fromPoly k r a, by simpa only [algebraMap_graphOpen, gdelta, toOpen_fromPoly] using h⟩
  · intro a b h
    have eqab : a = b := Subtype.ext (congrArg (fun x : openRing k r => (x : K k r)) h)
    subst b; exact ⟨0,rfl⟩

theorem common_open :
    IsLocalization.Away (gdelta k r) (openRing k r) ∧
      IsLocalization.Away (delta k r) (openRing k r) := ⟨inferInstance,inferInstance⟩

end GKGraph
