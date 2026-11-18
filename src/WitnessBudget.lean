import OriginalPole
noncomputable section
namespace G3Assembly
open Module GKGraph GKDivisor GKDivisor.Jet DVRMinimal
universe u
attribute [local instance] BadPole.cr BadPole.dom BadPole.dvr BadPole.alg
variable {k : Type u} [Field k] [CharZero k] {r : ℕ}
theorem witness_budget_impossible (W : RealWitness k r) (hr : 2≤r) (a b : ClosedF W.pole)
    (s t : Finset (ClosedF W.pole)) (hs : s.card≤r*r-2) (ht : t.card≤r*r-2)
    (h0 : reducedMatrices k r (graphAtClosure W.pole) 0=0)
    (h1 : ∀ i j, (reducedMatrices k r (graphAtClosure W.pole) 1 - a • 1) i j ∈ IntermediateField.adjoin k (s:Set _))
    (h2 : ∀ i j, (reducedMatrices k r (graphAtClosure W.pole) 2 - b • 1) i j ∈ IntermediateField.adjoin k (s:Set _))
    (h3 : ∀ i j, (reducedMatrices k r (graphAtClosure W.pole) 3 - a • 1) i j ∈ IntermediateField.adjoin k (t:Set _))
    (h4 : ∀ i j, (reducedMatrices k r (graphAtClosure W.pole) 4 - b • 1) i j ∈ IntermediateField.adjoin k (t:Set _)) :
    False := by
  have le := centered_parameter_bound k r (graphAtClosure W.pole) hr ![a,b] s t hs ht h0 h1 h2 h3 h4
  have cap := add_le_add_left le 1
  rw [W.count] at cap
  have hn : 3*r*r≤3*r*r-2+1 := by exact_mod_cast cap
  have hp : 2≤r*r := (by decide : 2≤2*2).trans (Nat.mul_le_mul hr hr)
  rw [Nat.mul_assoc] at hn
  omega
#print axioms witness_budget_impossible
end G3Assembly
