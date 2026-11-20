module

public import JordanDimension

@[expose] public section
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)

abbrev FreeIx := (h : Fin H) × (Fin (m h) × ((l : Fin H) ×
  (Fin (min (h.val+1) (l.val+1)) × Fin (m l))))
abbrev BlockIx := (h : Fin H) × (Fin (m h) × Fin (m h))

def slot (i : BlockIx m) : FreeIx m :=
  ⟨i.1,i.2.1,i.1,⟨i.1.val,by simp⟩,i.2.2⟩
theorem slot_inj : Function.Injective (slot m) := by
  rintro ⟨h,a,b⟩ ⟨l,c,d⟩ he
  cases he
  rfl

def coeff (z : Cent (K:=K) m) (i : FreeIx m) : K :=
  z.1 (gen m i.1 i.2.1) i.2.2.1
    ⟨i.2.2.2.1.val,lt_of_lt_of_le i.2.2.2.1.isLt (min_le_right _ _)⟩ i.2.2.2.2

theorem actual_entry (z : Cent (K:=K) m)
    (h l : Fin H) (a : Fin (m h)) (b : Fin (m l))
    (p : Fin (h.val+1)) (q : Fin (l.val+1)) :
    LinearMap.toMatrixAlgEquiv (coordBasis m) z.1 ⟨l,q,b⟩ ⟨h,p,a⟩ =
    if hj : q.val+(h.val-p.val) < min (h.val+1) (l.val+1)
    then coeff m z ⟨h,a,l,⟨q.val+(h.val-p.val),hj⟩,b⟩ else 0 := by
  rw [LinearMap.toMatrixAlgEquiv_apply,coord_repr,← gen_level]
  have hc := congrArg (fun g : Module.End K (V K m) => g (gen m h a))
      ((commJ m z).pow_right (h.val-p.val)).eq
  rw [show z.1 ((J m ^ (h.val-p.val)) (gen m h a)) =
     (J m ^ (h.val-p.val)) (z.1 (gen m h a)) from hc,Jpow]
  by_cases h₁ : q.val + (h.val - p.val) < min (h.val+1) (l.val+1)
  · rw [dite_eq_left (lt_min_iff.mp h₁).2,dite_eq_left h₁]
    rfl
  · rw [dite_eq_right h₁]
    split_ifs with ht
    · let k : Fin (l.val+1) := ⟨q.val + (h.val-p.val),ht⟩
      have hk : h.val+1 ≤ k.val := by dsimp [k]; rw [lt_min_iff] at h₁; omega
      let j : Fin (l.val+1) := ⟨k.val-(h.val+1),by have := k.isLt; omega⟩
      have hh : j.val+(h.val+1)=k.val := Nat.sub_add_cancel hk
      have he : (J m ^ (h.val+1)) (z.1 (gen m h a))=0 := (coeffOf m z h a).2
      have hs := congrFun (congrFun (congrFun he l) j) b
      rw [Jpow] at hs
      simpa [hh,k.isLt] using hs
    · rfl

theorem coeff_slot (z : Cent (K:=K) m) (i : BlockIx m) :
    coeff m z (slot m i) =
      rawBlock m (LinearMap.toMatrixAlgEquiv (coordBasis m) z.1) i.1 i.2.2 i.2.1 := by
  rcases i with ⟨h,a,b⟩
  change _ = LinearMap.toMatrixAlgEquiv (coordBasis m) z.1 ⟨h,0,b⟩ ⟨h,0,a⟩
  rw [actual_entry]
  simp [coeff,slot]

abbrev Residual := {i : FreeIx m // i ∉ Set.range (slot m)}

/-- Works with any collection of permitted scalars containing zero, so applies
directly to an arbitrary intermediate field without base-change machinery. -/
theorem entries_from_residual_and_blocks (Z : Matrix (Ix m) (Ix m) K)
    (hZ : Commute Z (matrixJ m)) (S : Set K) (h0 : 0 ∈ S)
    (hf : ∀ i : Residual m, coeff m (decode m Z hZ) i.1 ∈ S)
    (hb : ∀ (h : Fin H) (a b : Fin (m h)), rawBlock m Z h a b ∈ S) :
    ∀ i j, Z i j ∈ S := by
  let z := decode m Z hZ
  have hcoeff (i : FreeIx m) : coeff m z i ∈ S := by
    by_cases he : i ∈ Set.range (slot m)
    · obtain ⟨u,rfl⟩ := he
      rw [coeff_slot,show (LinearMap.toMatrixAlgEquiv (coordBasis m)) z.1= Z from encode_decode m Z hZ]
      exact hb _ _ _
    · exact hf ⟨i,he⟩
  rintro ⟨l,q,b⟩ ⟨h,p,a⟩
  rw [← encode_decode m Z hZ]
  rw [actual_entry]
  split <;> first | exact hcoeff _ | exact h0

theorem residual_card :
    Nat.card (Residual m) = finrank K (Cent (K:=K) m) - ∑ h, m h ^ 2 := by
  classical
  rw [Nat.card_eq_fintype_card,centralizer_dimension]
  change Fintype.card ((Set.range (slot m))ᶜ : Set (FreeIx m)) = _
  rw [Fintype.card_compl_set,Set.card_range_of_injective (slot_inj m)]
  simp [FreeIx,BlockIx,Fintype.card_sigma,pow_two]
/-- Exact finite list for field-of-definition or a transcendence-degree budget.
No coordinate of a change-of-basis matrix occurs in this list. -/
theorem literal_parameter_list (Z : Matrix (Ix m) (Ix m) K) (hZ : Commute Z (matrixJ m)) :
    ∃ f : Fin (finrank K (Cent (K:=K) m) - ∑ h, m h ^ 2) → K,
      ∀ S : Set K, 0 ∈ S → (∀ i, f i ∈ S) →
      (∀ (h : Fin H) (a b : Fin (m h)), rawBlock m Z h a b ∈ S) →
      ∀ i j, Z i j ∈ S := by
  classical
  let e := Fintype.equivFinOfCardEq (α:=Residual m) (by
    simpa only [Nat.card_eq_fintype_card] using residual_card (K:=K) m)
  refine ⟨fun i => coeff m (decode m Z hZ) (e.symm i).1,?_⟩
  intro S h0 hf hb
  apply entries_from_residual_and_blocks m Z hZ S h0 _ hb
  intro i
  simpa using hf (e i)
end JordanPrimitive
