module

public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic

@[expose] public section
noncomputable section
namespace GKRational
variable {A K O : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing O] [IsDomain O]

def rat (a b : A) : K := algebraMap A K a / algebraMap A K b
abbrev adj (a b : A) := Algebra.adjoin A ({rat (K := K) a b} : Set K)
def q (a b : A) : adj (K := K) a b := ⟨rat a b, Algebra.subset_adjoin rfl⟩
abbrev opn (b : A) (hb : b ≠ 0) := Localization.subalgebra.ofField K (Submonoid.powers b)
  (powers_le_nonZeroDivisors_of_noZeroDivisors hb)
theorem toOpen (a b : A) (hb : b ≠ 0) : adj (K := K) a b ≤ opn b hb := by
  apply Algebra.adjoin_le
  rintro _ rfl
  exact ⟨a,b,Submonoid.mem_powers _, div_eq_mul_inv ..⟩

omit [IsDomain A] in
theorem qmul (a b : A) (hb : b ≠ 0) :
    q (K := K) a b * algebraMap A (adj a b) b = algebraMap A (adj a b) a := by
  apply Subtype.ext
  exact div_mul_cancel₀ _ ((IsFractionRing.to_map_eq_zero_iff.not).mpr hb)

variable (f : A →+* O) (a b : A) (hb : f b ≠ 0)
omit [IsDomain A] [IsDomain O] in
include hb in
theorem bne : b ≠ 0 := fun e => hb (by rw [e,map_zero])

def fracEval : adj (K := K) a b →+* FractionRing O :=
  let g := (algebraMap O (FractionRing O)).comp f
  let hgb : IsUnit (g b) := isUnit_iff_ne_zero.mpr ((IsFractionRing.to_map_eq_zero_iff.not).2 hb)
  (IsLocalization.Away.lift b (S := opn (K := K) b (bne f b hb)) hgb).comp
    (Subalgebra.inclusion (toOpen a b (bne f b hb))).toRingHom

theorem fracEval_base (x : A) : fracEval (K := K) f a b hb (algebraMap A (adj a b) x) =
    algebraMap O (FractionRing O) (f x) := by
  let g := (algebraMap O (FractionRing O)).comp f
  have hg : IsUnit (g b) := isUnit_iff_ne_zero.mpr ((IsFractionRing.to_map_eq_zero_iff.not).2 hb)
  exact IsLocalization.Away.lift_eq (S := opn (K := K) b (bne f b hb)) b hg x

variable (w : O) (hw : w * f b = f a)

include hw in
theorem fracEval_q : fracEval (K := K) f a b hb (q a b) = algebraMap O (FractionRing O) w := by
  have h := congrArg (fracEval (K := K) f a b hb) (qmul a b (bne f b hb))
  rw [map_mul, fracEval_base,fracEval_base,←hw,map_mul] at h
  exact mul_right_cancel₀ ((IsFractionRing.to_map_eq_zero_iff.not).2 hb) h

omit [IsDomain A] [IsFractionRing A K] in
private theorem top_q :
    Algebra.adjoin A ({q (K := K) a b} : Set (adj a b)) = ⊤ := by
  apply Subalgebra.map_injective (f := (adj a b).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Set.image_singleton,Algebra.map_top,Subalgebra.range_val]
  rfl

include hw in
theorem fracEval_range (x : adj (K := K) a b) :
    fracEval f a b hb x ∈ (algebraMap O (FractionRing O)).range := by
  let T : Subalgebra A (adj (K := K) a b) :=
    { (algebraMap O (FractionRing O)).range.comap (fracEval f a b hb) with
      algebraMap_mem' := fun y => ⟨f y, (fracEval_base f a b hb y).symm⟩ }
  have hq : q a b ∈ T := ⟨w, (fracEval_q f a b hb w hw).symm⟩
  have ht : ⊤ ≤ T := by
    rw [←top_q a b]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hq)
  exact ht (show x ∈ (⊤ : Subalgebra A _) from Algebra.mem_top)

/-- Descent along an injective inclusion. No injectivity is assumed for the
specialized map out of the original universal graph. -/
def descend {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
    (h : C →+* D) (hi : Function.Injective h) (g : B →+* D)
    (hg : ∀ x, g x ∈ h.range) : B →+* C where
  toFun x := (hg x).choose
  map_zero' := hi (by rw [(hg 0).choose_spec,map_zero,map_zero])
  map_one' := hi (by rw [(hg 1).choose_spec,map_one,map_one])
  map_add' x y := hi (by rw [(hg (x+y)).choose_spec,map_add,map_add,(hg x).choose_spec,(hg y).choose_spec])
  map_mul' x y := hi (by rw [(hg (x*y)).choose_spec,map_mul,map_mul,(hg x).choose_spec,(hg y).choose_spec])

def specialize : adj (K := K) a b →+* O :=
  descend (algebraMap O (FractionRing O)) (IsFractionRing.injective _ _)
    (fracEval f a b hb) (fracEval_range f a b hb w hw)

theorem spec_base (x : A) :
    specialize (K := K) f a b hb w hw (algebraMap A (adj a b) x) = f x := by
  apply IsFractionRing.injective O (FractionRing O)
  exact ((fracEval_range (K := K) f a b hb w hw _).choose_spec).trans (fracEval_base f a b hb x)

theorem spec_q : specialize (K := K) f a b hb w hw (q a b) = w := by
  apply IsFractionRing.injective O (FractionRing O)
  exact ((fracEval_range (K := K) f a b hb w hw _).choose_spec).trans (fracEval_q f a b hb w hw)

include hw hb in
theorem q_nonunit (hn : ¬ IsUnit w) : ¬ IsUnit (q (K := K) a b) := by
  intro hu
  exact hn ((spec_q (K := K) f a b hb w hw) ▸ hu.map (specialize f a b hb w hw))

omit [IsDomain A] in
theorem q_ne_zero (ha : a ≠ 0) (hb' : b ≠ 0) : q (K := K) a b ≠ 0 := by
  intro e
  exact div_ne_zero ((IsFractionRing.to_map_eq_zero_iff.not).2 ha)
    ((IsFractionRing.to_map_eq_zero_iff.not).2 hb') (congrArg Subtype.val e)
end GKRational
