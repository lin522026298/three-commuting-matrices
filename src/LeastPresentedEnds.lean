import SourceEndFrames
import EndCoordinateCriterion
import GKGraphCore
set_option linter.style.haveILetI false
noncomputable section
namespace GKEnds
universe u
open Module LinearMap DivisorG3 PowerSeries
open Gerstenhaber.FourBlocks.HeadBounds Gerstenhaber.FourBlocks.MinimalSource
open Gerstenhaber.FourBlocks.PrimaryDecomposition
open DVRMinimal
variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] (r : ℕ)
variable (S : Fin 6 → GKGraph.Mat (O k) r)
abbrev r0 (l : Fin 6) := redM (S l)

/-- A presentation need not start minimal: the inequality on all smaller widths
forces it to become minimal and hence kills EVERY constant entry of P. The very
same translations then work on both ends, and primed rows act on the true tail. -/
theorem least_presented_ends (hp : (S 0).det≠0)
    (sy : S 1*S 0=S 0*S 3) (sz : S 2*S 0=S 0*S 4)
    [FiniteDimensional k (QP (S 0))]
    (T : Fin 3 → End k (QP (S 0))) (hc : ∀ i j, Commute (T i) (T j))
    (h0 : T 0=xop (S 0))
    (h1 : ∀ v, T 1 ((S 0).mulVecLin.range.mkQ v)=(S 0).mulVecLin.range.mkQ ((S 1).mulVecLin v))
    (h2 : ∀ v, T 2 ((S 0).mulVecLin.range.mkQ v)=(S 0).mulVecLin.range.mkQ ((S 2).mulVecLin v))
    (hnil : IsNilpotent (T 0)) (bad : finrank k (QP (S 0)) < finrank k (Generated T))
    (small : ∀ j<r, SafeEverywhere.{u} j) :
    r0 r S 0=0 ∧ ∃ a b : k, SubregularPair (r0 r S 1-a • 1) (r0 r S 2-b • 1) ∧
      SubregularPair (r0 r S 3-a • 1) (r0 r S 4-b • 1) := by
  have le : finrank k (xop (S 0)).ker ≤ r := by simpa only [Fintype.card_fin] using width_le (S 0)
  have eq : finrank k (xop (S 0)).ker = r := by
    apply le_antisymm le
    by_contra! lt
    have hh := small _ lt k (QP (S 0)) T hc hnil (congrArg (fun f : End k (QP (S 0)) => finrank k f.ker) h0)
    exact (not_lt_of_ge hh) bad
  have w : finrank k (xop (S 0)).ker=Fintype.card (Fin r) := eq.trans (Fintype.card_fin _).symm
  refine ⟨constant_P_zero (S 0) w,?_⟩
  obtain ⟨c,hc0,hn,wide⟩ := least_bad_shifted_two_ends T hc hnil bad (fun j hj => small j (by rwa [h0,eq] at hj))
  let U := FiniteNilTriple.of (QP (S 0)) (shifted T c) (shifted_commute T c hc) hn
  letI : CommRing (SourceAlgebra U) := sourceAlgebra_commRing U
  letI : Module (SourceAlgebra U) (QP (S 0)) := (inferInstance : Module (SourceAlgebra U) U.Carrier)
  letI : IsScalarTower k (SourceAlgebra U) (QP (S 0)) := sourceAlgebra_tower U
  let t := sourceRoot U 0
  let y := sourceRoot U 1
  let z := sourceRoot U 2
  have xt (v : QP (S 0)) : t • v = (X : O k) • v := by
    change (T 0 - c 0 • 1) v = _
    rw [hc0,zero_smul,sub_zero,h0]; rfl
  obtain ⟨H,D,act⟩ := centered_frames (A:=SourceAlgebra U) (S 0) t xt w hp
  have actY := act (S 1) (S 3) sy (c 1) y (fun v => by
    change T 1 _ - c 1 • _ = _; rw [h1]; rfl)
  have actZ := act (S 2) (S 4) sz (c 2) z (fun v => by
    change T 2 _ - c 2 • _ = _; rw [h2]; rfl)
  exact ⟨c 1,c 2,
    coordinate_criterion H _ _ y z (sourceRoot_nilpotent U 1) (sourceRoot_nilpotent U 2) actY.1 actZ.1 wide.1,
    coordinate_criterion D _ _ y z (sourceRoot_nilpotent U 1) (sourceRoot_nilpotent U 2) actY.2 actZ.2 wide.2⟩

#print axioms least_presented_ends
end GKEnds
