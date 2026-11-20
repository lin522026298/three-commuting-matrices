module

public import RealCenters
public import WitnessBudget
public import ActualPairParameters
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section
noncomputable section
namespace G3Assembly
open Module GKGraph GKDivisor GKDivisor.Jet GKEnds DVRMinimal
attribute [local instance] BadPole.cr BadPole.dom BadPole.dvr BadPole.alg
/-- Does not assume an orbit dimension, Jordan model, coordinate budget, divisor,
geometric conjecture, local quotient bound or small-n matrix result. -/
theorem not_actual_witness {k : Type} [Field k] [IsAlgClosed k] {r : ℕ} (W : RealWitness k r)
    (hr : 2≤r) (small : ∀ j<r, SafeEverywhere.{0} j) : False := by
  obtain ⟨h0,a,b,ha,hb⟩ := actual_center_pairs W (by omega) small
  obtain ⟨s,hs,hs1,hs2⟩ := GKGauge.subregular_pair_parameters (k:=k) _ _ ha.comm ha.nilY ha.nilZ ha.width
  obtain ⟨t,ht,ht1,ht2⟩ := GKGauge.subregular_pair_parameters (k:=k) _ _ hb.comm hb.nilY hb.nilZ hb.width
  exact witness_budget_impossible W hr a b s t hs ht h0 hs1 hs2 ht1 ht2

/-- Literal arbitrary-size commuting triples over a algebraically closed
field in Type 0, including C. No chosen nilpotent coordinate or joint-primary form. -/
theorem matrix_triple_bound (k : Type) [Field k] [IsAlgClosed k] (n : ℕ)
    (A : Fin 3 → Matrix (Fin n) (Fin n) k) (hc : ∀ i j, Commute (A i) (A j)) :
    finrank k (Algebra.adjoin k (Set.range A))≤n := by
  by_contra! bad
  obtain ⟨r,hr,_,small,B,⟨W⟩⟩ := original_matrix_pole k A hc bad
  exact not_actual_witness W hr small

theorem complex_triple_bound (n : ℕ) (A : Fin 3 → Matrix (Fin n) (Fin n) ℂ)
    (hc : ∀ i j, Commute (A i) (A j)) : finrank ℂ (Algebra.adjoin ℂ (Set.range A))≤n :=
  matrix_triple_bound ℂ n A hc
/-- Direct three-name, ordinary complex matrix formulation, including n=0. -/
theorem complex_three_matrices {n : ℕ} (X Y Z : Matrix (Fin n) (Fin n) ℂ)
    (hxy : Commute X Y) (hxz : Commute X Z) (hyz : Commute Y Z) :
    finrank ℂ (Algebra.adjoin ℂ ({X,Y,Z}:Set _))≤n := by
  let S : Fin 3 → Matrix (Fin n) (Fin n) ℂ := ![X,Y,Z]
  have hc (i j : Fin 3) : Commute (S i) (S j) := by
    fin_cases i <;> fin_cases j <;>
      first | exact Commute.refl _ | exact hxy | exact hxz | exact hyz | exact hxy.symm | exact hxz.symm | exact hyz.symm
  have range : Set.range S=({X,Y,Z}:Set _) := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩; fin_cases i <;> simp [S]
    · rintro (h|h|h)
      · exact ⟨0,h.symm⟩
      · exact ⟨1,h.symm⟩
      · exact ⟨2,(Set.mem_singleton_iff.mp h).symm⟩
  exact range ▸ complex_triple_bound n S hc
#print axioms complex_three_matrices
#print axioms not_actual_witness
#print axioms matrix_triple_bound
#print axioms complex_triple_bound
end G3Assembly
