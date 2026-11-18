import ActualMinimalEnds
namespace DVRMinimal
open Module Gerstenhaber.FourBlocks.PrimaryDecomposition
universe u
structure BadAt (r : ℕ) where
  k : Type u
  [field : Field k]
  [closed : IsAlgClosed k]
  [char0 : CharZero k]
  W : Type u
  [group : AddCommGroup W]
  [module_ : Module k W]
  [finite : FiniteDimensional k W]
  T : Fin 3 → Module.End k W
  hc : ∀ i j, Commute (T i) (T j)
  hn : IsNilpotent (T 0)
  width : finrank k (T 0).ker=r
  bad : finrank k W<finrank k (Generated T)
attribute [instance] BadAt.field BadAt.closed BadAt.char0 BadAt.group BadAt.module_ BadAt.finite

theorem badAt_iff (r : ℕ) : Nonempty (BadAt.{u} r) ↔ ¬SafeEverywhere.{u} r := by
  constructor
  · rintro ⟨B⟩ safe
    exact (not_lt_of_ge (safe B.k B.W B.T B.hc B.hn B.width)) B.bad
  · classical
    intro h
    by_contra hn
    apply h
    intro k _ _ _ W _ _ _ T hc ht hr
    apply le_of_not_gt
    intro hb
    exact hn ⟨{k:=k,W:=W,T:=T,hc:=hc,hn:=ht,width:=hr,bad:=hb}⟩

/-- A completely arbitrary bad triple of actual matrices, without joint-primary
or nilpotence supplied, furnishes a nonempty least width r across all algebraically
closed characteristic-zero fields, with real witnesses of that width. -/
theorem arbitrary_matrix_to_least (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (A : Fin 3 → Matrix (Fin n) (Fin n) k) (hc : ∀ i j,Commute (A i) (A j))
    (hb : n<finrank k (Algebra.adjoin k (Set.range A))) :
    ∃ r ≤ n, Nonempty (BadAt.{u} r) ∧ ∀ j<r,SafeEverywhere.{u} j := by
  classical
  have hex : ∃ j ≤ n, ¬ SafeEverywhere.{u} j := by
    by_contra! h
    have pay := matrix_triple_bound_of_nilpotent_bound (K:=k) n (by
      intro W _ _ _ T ht hn hw
      exact h _ hw k W T ht (hn 0) rfl) n A hc (fun a => by
        have hh := (Matrix.toLin' (A 0-a • 1)).ker.finrank_le
        simpa only [Module.finrank_pi,Fintype.card_fin] using hh)
    exact (not_lt_of_ge pay) hb
  obtain ⟨j,hj,hbad⟩ := hex
  obtain ⟨r,hr,fail,hmin⟩ := first_failure_any_field hbad
  exact ⟨r,hr.trans hj,(badAt_iff r).mpr fail,hmin⟩

open Gerstenhaber.FourBlocks.HeadBounds Gerstenhaber.FourBlocks.MinimalSource

theorem twoEnds_width {k : Type u} [Field k] (A : FiniteNilTriple k) (hh : TwoEnds A) :
    2 ≤ finrank k (A.operator 0).ker := by
  let t := sourceRoot A 0
  let y := sourceRoot A 1
  let H := ActualHead (M:=A.Carrier) t
  have rank := (Algebra.lsmul k k H y).ker.finrank_le
  have h := hh.1.trans rank
  change 2≤finrank k (ActualHead (M:=A.Carrier) t) at h
  rw [actualHead_finrank] at h
  exact h

theorem minimal_width_at_least_two {r : ℕ} (B : BadAt.{u} r)
    (small : ∀ j<r,SafeEverywhere.{u} j) : 2 ≤ r := by
  have sm : ∀j<finrank B.k (B.T 0).ker,SafeEverywhere.{u} j := by rw [B.width];exact small
  obtain ⟨chi,h0,hn,hh⟩ := least_bad_shifted_two_ends B.T B.hc B.hn B.bad sm
  have h := twoEnds_width _ hh
  change 2≤finrank B.k (shifted B.T chi 0).ker at h
  have hz : shifted B.T chi 0 = B.T 0 := by
    change B.T 0 - chi 0 • 1 = B.T 0
    rw [h0,zero_smul,sub_zero]
  rw [hz,B.width] at h; exact h

theorem arbitrary_matrix_to_least_positive (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (A : Fin 3 → Matrix (Fin n) (Fin n) k) (hc : ∀ i j,Commute (A i) (A j))
    (hb : n<finrank k (Algebra.adjoin k (Set.range A))) :
    ∃ r, 2≤r ∧ r≤n ∧ Nonempty (BadAt.{u} r) ∧ ∀ j<r,SafeEverywhere.{u} j := by
  obtain ⟨r,rn,⟨B⟩,small⟩ := arbitrary_matrix_to_least k n A hc hb
  exact ⟨r,minimal_width_at_least_two B small,rn,⟨B⟩,small⟩

#print axioms arbitrary_matrix_to_least_positive
#print axioms badAt_iff
#print axioms arbitrary_matrix_to_least
end DVRMinimal
