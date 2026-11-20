module

public import MinimalPrimary
public import RegularEnds
public import Gerstenhaber.FourBlocks.MinimalSource.NilThreeSource

@[expose] public section
noncomputable section
namespace DVRMinimal
open Module LinearMap
open Gerstenhaber.FourBlocks.PrimaryDecomposition Gerstenhaber.FourBlocks.MinimalSource
open Gerstenhaber.FourBlocks.HeadBounds

universe u
def SafeEverywhere (r : ℕ) : Prop := ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k], SafeAt k r

theorem first_failure_any_field {s : ℕ} (hf : ¬SafeEverywhere.{u} s) :
    ∃ r ≤ s, (¬SafeEverywhere.{u} r) ∧ ∀ j<r, SafeEverywhere.{u} j := by
  classical
  have ex : ∃ r, ¬SafeEverywhere.{u} r := ⟨s,hf⟩
  exact ⟨Nat.find ex,Nat.find_min' ex hf,Nat.find_spec ex,fun j hj => not_not.mp (Nat.find_min ex hj)⟩

theorem ker_pos {k W : Type u} [Field k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] [Nontrivial W] (y : Module.End k W) (hy : IsNilpotent y) :
    0<finrank k y.ker := by
  obtain ⟨w,hw,hne⟩ := nil_kernel_vector y hy
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨w,hw⟩,fun eq => hne (congrArg Subtype.val eq)⟩

variable {k : Type u} [Field k]
def TwoEnds (X : FiniteNilTriple k) : Prop :=
    let t := sourceRoot X 0
    let y := sourceRoot X 1
    2 ≤ finrank k (Algebra.lsmul k k (ActualHead (M:=X.Carrier) t) y).ker ∧
      2 ≤ finrank k (Algebra.lsmul k k (tKernel (M:=X.Carrier) t) y).ker

theorem nil_failure_two_at_each_end (X : FiniteNilTriple k)
    (hb : finrank k X.Carrier < finrank k (SourceAlgebra X)) : TwoEnds X := by
  let t := sourceRoot X 0
  let y := sourceRoot X 1
  let T := tKernel (M:=X.Carrier) t
  let H := ActualHead (M:=X.Carrier) t
  letI : Nontrivial X.Carrier := sourceCarrier_nontrivial_of_failure X hb
  have ht := sourceRoot_nilpotent X 0
  have hy := sourceRoot_nilpotent X 1
  have hk := ker_pos (X.operator 0) (X.nilpotent 0)
  letI : Nontrivial H := Module.nontrivial_of_finrank_pos (R:=k) (by
    change 0<finrank k (ActualHead (M:=X.Carrier) t); rw [actualHead_finrank]; exact hk)
  letI : FiniteDimensional k T := FiniteDimensional.of_injective
    ((tKernel (M:=X.Carrier) t).subtype.restrictScalars k) (tKernel (M:=X.Carrier) t).injective_subtype
  have ⟨w,hw,wn⟩ := nil_kernel_vector (X.operator 0) (X.nilpotent 0)
  letI : Nontrivial T := nontrivial_of_ne (⟨w,hw⟩ : T) 0 (fun eq => wn (congrArg Subtype.val eq))
  have bpH := ker_pos (Algebra.lsmul k k H y) (hy.map (Algebra.lsmul k k H))
  have bpT := ker_pos (Algebra.lsmul k k T y) (hy.map (Algebra.lsmul k k T))
  have nH : finrank k (Algebra.lsmul k k H y).ker ≠ 1 := by
    intro he; have b := regular_head_pay (k:=k) (W:=X.Carrier) t y ht hy he
    rw [sourceActionImage_eq] at b; exact (not_lt_of_ge b) hb
  have nT : finrank k (Algebra.lsmul k k T y).ker ≠ 1 := by
    intro he; have b := regular_tail_pay (k:=k) (W:=X.Carrier) t y ht hy he
    rw [sourceActionImage_eq] at b; exact (not_lt_of_ge b) hb
  change 2≤finrank k (Algebra.lsmul k k H y).ker ∧ 2≤finrank k (Algebra.lsmul k k T y).ker
  omega

variable [IsAlgClosed k] [CharZero k] {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
theorem least_bad_shifted_two_ends (T : Fin 3 → Module.End k W)
    (hc : ∀ i j, Commute (T i) (T j)) (hn : IsNilpotent (T 0))
    (bad : finrank k W < finrank k (Generated T))
    (small : ∀ j < finrank k (T 0).ker, SafeEverywhere.{u} j) :
    ∃ (chi : Fin 3 → k) (_ : chi 0=0) (hnil : ∀ i,IsNilpotent (shifted T chi i)),
      TwoEnds (FiniteNilTriple.of W (shifted T chi) (shifted_commute T chi hc) hnil) := by
  obtain ⟨χ,hχ⟩ := least_bad_single_spectrum T hc hn bad (fun j hj => small j hj k)
  let c := Function.update χ 0 0
  have h0 : c 0=0 := Function.update_self ..
  have hn' (i) : IsNilpotent (shifted T c i) := by
    by_cases h : i=0
    · subst i; simpa only [shifted,h0,zero_smul,sub_zero] using hn
    · simpa only [shifted,c,Function.update_of_ne h] using hχ i
  refine ⟨c,h0,hn',nil_failure_two_at_each_end _ ?_⟩
  change finrank k W < finrank k (Generated (shifted T c))
  rwa [adjoin_shifted]

#print axioms first_failure_any_field
#print axioms nil_failure_two_at_each_end
#print axioms least_bad_shifted_two_ends
end DVRMinimal
