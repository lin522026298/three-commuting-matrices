import OriginalPole
import StrictEndCoordinates
noncomputable section
namespace G3Assembly
open Module GKGraph GKDivisor GKDivisor.Jet GKEnds DVRMinimal
universe u
attribute [local instance] BadPole.cr BadPole.dom BadPole.dvr BadPole.alg
variable {k : Type u} [Field k] [CharZero k] {r : ℕ}
theorem actual_center_pairs (W : RealWitness k r) (hr : 0<r) (small : ∀ j<r,SafeEverywhere.{u} j) :
    let R := reducedMatrices k r (graphAtClosure W.pole)
    R 0=0 ∧ ∃ a b : ClosedF W.pole, SubregularPair (R 1-a • 1) (R 2-b • 1) ∧
      SubregularPair (R 3-a • 1) (R 4-b • 1) := by
  let _ : CharZero (ClosedF W.pole) := charZero_of_injective_algebraMap (algebraMap k _).injective
  have hs := strict_end_coordinates r W.arc.T W.arc.relations W.arc.det_ne hr W.s W.arc.strict small
  have eq (i : Fin 6) : reducedMatrices k r (graphAtClosure W.pole) i = r0 r W.arc.T i := by
    ext a b
    exact (congrFun W.same_entries (i,a,b)).symm
  dsimp only
  simp only [eq]
  exact hs
#print axioms actual_center_pairs
end G3Assembly
