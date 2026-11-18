import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Linarith
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! Arbitrary multiplicities, including empty levels. Group h has strings of
length h+1. The primitive coordinates below are taken on the socle flag,
not on the whole head or on arbitrarily chosen diagonal submatrices. -/
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)
abbrev V (K : Type*) {H : ℕ} (m : Fin H → ℕ) :=
  (h : Fin H) → Fin (h.val+1) → (Fin (m h) → K)
abbrev B (K : Type*) {H : ℕ} (m : Fin H → ℕ) [Field K] :=
  (h : Fin H) → Module.End K (Fin (m h) → K)

def J : Module.End K (V K m) where
  toFun v h j := if hj : j.val + 1 < h.val + 1 then v h ⟨j.val+1,hj⟩ else 0
  map_add' v w := by ext h j a; dsimp; split <;> simp
  map_smul' u v := by ext h j a; dsimp; split <;> simp

theorem Jpow (k : ℕ) (v : V K m) (h : Fin H) (j : Fin (h.val+1)) :
    ((J m ^ k) v) h j =
    if hj : j.val+k < h.val+1 then v h ⟨j.val+k,hj⟩ else 0 := by
  induction k generalizing j with
  | zero => simp [j.isLt]
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp]
    change (if hc : j.val+1 < h.val+1 then ((J m ^ k) v) h ⟨j.val+1,hc⟩ else 0) = _
    split_ifs with hc hd
    · rw [ih]; simp [Nat.add_assoc, Nat.add_comm 1 k, hd]
    · rw [ih]; simp [show ¬ (j.val+1+k < h.val+1) by omega]
    · omega
    · rfl

theorem J_nilpotent : IsNilpotent (J (K:=K) m) := by
  refine ⟨H,?_⟩
  apply LinearMap.ext
  intro v
  funext h j
  rw [Jpow, dite_eq_right (by have := h.isLt; omega)]
  rfl

abbrev Cent := Subalgebra.centralizer K ({J (K:=K) m} : Set (Module.End K (V K m)))
theorem commJ (z : Cent (K:=K) m) : Commute (z:Module.End K (V K m)) (J m) := by
  exact (z.property _ (Set.mem_singleton _)).symm

def Fl (k : ℕ) (v : V K m) : Prop :=
  ∀ (h : Fin H) (j : Fin (h.val+1)), j.val ≠ 0 ∨ h.val < k → v h j = 0

/-- The coordinate flag is intrinsic: soc J intersect image J^k. -/
theorem fl_iff (k : ℕ) (v : V K m) :
    Fl m k v ↔ J m v = 0 ∧ ∃ w, (J m ^ k) w = v := by
  constructor
  · intro hv
    constructor
    · funext h j
      change (if hc : j.val + 1 < h.val+1 then v h ⟨j.val+1,hc⟩ else 0) = 0
      split <;> first | apply hv; exact Or.inl (Nat.succ_ne_zero _) | rfl
    · refine ⟨fun h i => if i.val = k then v h 0 else 0,?_⟩
      funext h j
      rw [Jpow]
      by_cases hz : j.val = 0
      · obtain rfl : j = 0 := Fin.ext hz
        simp only [Fin.val_zero,Nat.zero_add]
        split_ifs with hh
        · rfl
        · exact (hv h 0 (Or.inr (by omega))).symm
      · split_ifs with hh he
        · change j.val+k = k at he; omega
        · exact (hv h j (Or.inl hz)).symm
        · exact (hv h j (Or.inl hz)).symm
  · rintro ⟨hn,w,hw⟩ h j (hj|hh)
    · let i : Fin (h.val+1) := ⟨j.val-1,by have := j.isLt; omega⟩
      have hi : i.val+1 = j.val := by dsimp [i]; omega
      have hc := congrFun (congrFun hn h) i
      change (if hx : i.val+1<h.val+1 then v h ⟨i.val+1,hx⟩ else 0) = 0 at hc
      simpa [hi,j.isLt] using hc
    · rw [← hw,Jpow,dite_eq_right (by omega)]

theorem map_fl (z : Cent (K:=K) m) (k : ℕ) {v : V K m} (hv : Fl m k v) :
    Fl m k (z.1 v) := by
  rw [fl_iff] at hv ⊢
  obtain ⟨hzero,w,rfl⟩ := hv
  constructor
  · calc
      J m (z.1 ((J m ^ k) w)) = z.1 (J m ((J m ^ k) w)) :=
        congrArg (fun f : Module.End K (V K m) => f ((J m ^ k) w)) (commJ m z).eq.symm
      _ = 0 := by rw [hzero,map_zero]
  · exact ⟨z.1 w,congrArg (fun f : Module.End K (V K m) => f w)
        ((commJ m z).pow_right k).eq.symm⟩

def put (h : Fin H) : (Fin (m h) → K) →ₗ[K] V K m :=
  (LinearMap.single K _ h).comp (LinearMap.single K (fun _ : Fin (h.val+1) => Fin (m h) → K) 0)

@[simp] theorem put_at (h : Fin H) (u : Fin (m h) → K) :
    put m h u h 0 = u := by simp [put]
theorem put_fl (h : Fin H) (u : Fin (m h) → K) : Fl m h.val (put m h u) := by
  intro l j hj
  by_cases he : l=h
  · subst l
    have hj' : j ≠ 0 := fun hh => by subst j; simp at hj
    simp [put,Pi.single_eq_of_ne hj']
  · simp [put,Pi.single_eq_of_ne he]

theorem discard (h : Fin H) (v : V K m) (hv : Fl m h.val v) :
    Fl m (h.val+1) (v - put m h (v h 0)) := by
  intro l j hj
  by_cases hh : l=h
  · subst l
    by_cases hz : j=0
    · subst j; simp
    · have hj' : j.val ≠ 0 := fun e => hz (Fin.ext e)
      simp [put,Pi.single_eq_of_ne hz,hv h j (Or.inl hj')]
  · have hl : l.val ≠ h.val := fun e => hh (Fin.ext e)
    have hclean : j.val ≠ 0 ∨ l.val < h.val := by rcases hj with hj|hj <;> omega
    simp [put,Pi.single_eq_of_ne hh,hv l j hclean]

def part (z : Cent (K:=K) m) (h : Fin H) : Module.End K (Fin (m h) → K) :=
  (LinearMap.proj 0).comp ((LinearMap.proj h).comp (z.1.comp (put m h)))

theorem eval_fl (z : Cent (K:=K) m) (h : Fin H) (v : V K m) (hv : Fl m h.val v) :
    z.1 v h 0 = part m z h (v h 0) := by
  have he := map_fl m z (h.val+1) (discard m h v hv) h 0 (Or.inr (Nat.lt_succ_self _))
  change (z.1 (v - put m h (v h 0))) h 0 = 0 at he
  rw [map_sub] at he
  exact sub_eq_zero.mp he

def primitive : Cent (K:=K) m →ₐ[K] B K m where
  toFun := part m
  map_one' := by funext h; apply LinearMap.ext; intro u; exact put_at m h u
  map_mul' z w := by
    funext h
    apply LinearMap.ext
    intro u
    exact eval_fl m z h (w.1 (put m h u)) (map_fl m w _ (put_fl m h u))
  map_zero' := by funext h; apply LinearMap.ext; intro u; rfl
  map_add' z w := by funext h; apply LinearMap.ext; intro u; rfl
  commutes' c := by
    funext h
    apply LinearMap.ext
    intro u
    change c • put m h u h 0 = c • u
    rw [put_at]

/-- Same matrix at every depth of its own strings; zero between distinct lengths. -/
def liftEnd (f : B K m) : Module.End K (V K m) where
  toFun v h i := f h (v h i)
  map_add' v w := by funext h i; exact (f h).map_add _ _
  map_smul' a v := by funext h i; exact (f h).map_smul a _

theorem lift_mem (f : B K m) : liftEnd m f ∈ Cent (K:=K) m := by
  apply (Subalgebra.mem_centralizer_iff K).mpr
  rintro _ ⟨rfl⟩
  apply LinearMap.ext
  intro v
  funext h j
  change (if hq : j.val+1<h.val+1 then f h (v h ⟨j.val+1,hq⟩) else 0) =
    f h (if hq : j.val+1<h.val+1 then v h ⟨j.val+1,hq⟩ else 0)
  split_ifs <;> simp

def sectionHom : B K m →ₐ[K] Cent (K:=K) m where
  toFun f := ⟨liftEnd m f,lift_mem m f⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem primitive_section (f : B K m) :
    primitive m (sectionHom m f) = f := by
  funext h
  apply LinearMap.ext
  intro v
  change f h (put m h v h 0) = f h v
  rw [put_at]

theorem primitive_surjective : Function.Surjective (primitive (K:=K) m) :=
  fun f => ⟨sectionHom m f, primitive_section m f⟩

/-- Nilpotence of the actual endomorphism, not an assumption on its components. -/
theorem part_nilpotent (z : Cent (K:=K) m) (hz : IsNilpotent z.1) (h : Fin H) :
    IsNilpotent (part m z h) := by
  obtain ⟨n,hn⟩ := hz
  have hc : z ^ n = 0 := Subtype.ext (by simpa using hn)
  have he := congrArg (fun w : Cent (K:=K) m => primitive m w h) hc
  simpa [map_pow] using (show IsNilpotent (part m z h) from
    ⟨n,by change (primitive m z h)^n=0; simpa [map_pow] using he⟩)

theorem target_finrank : finrank K (B K m) = ∑ h, m h ^ 2 := by
  change finrank K ((h : Fin H) → Module.End K (Fin (m h) → K)) = _
  rw [finrank_pi_fintype]
  simp only [Module.End,finrank_linearMap,finrank_pi,Fintype.card_fin,pow_two]

/-- All kernel parameters are free linear coordinates, dimension c−Σm_h². -/
theorem primitive_rank_nullity :
    (∑ h, m h ^ 2) + finrank K (LinearMap.ker (primitive (K:=K) m).toLinearMap) =
    finrank K (Cent (K:=K) m) := by
  have e := LinearMap.finrank_range_add_finrank_ker (K:=K)
    (V:=Cent (K:=K) m) (V₂:=B K m) (primitive (K:=K) m).toLinearMap
  rw [LinearMap.range_eq_top.mpr (primitive_surjective (K:=K) m),finrank_top,target_finrank] at e
  exact e

end JordanPrimitive
