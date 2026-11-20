module

public import PolePrime
public import Mathlib.RingTheory.IntegralClosure.GoingDown

@[expose] public section

noncomputable section
namespace GKDivisor
/-- Contraction of a height-one prime along a finite integral dominant extension of
normal base domains, with no going-down input supplied beyond normality. -/
theorem heightOne_under {S R : Type*} [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [IsNoetherianRing S] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra S R] [FaithfulSMul S R] [Algebra.IsIntegral S R]
    (P : Ideal R) [P.IsPrime] (h : P.height = 1) : (P.under S).height = 1 := by
  have hn := P.under_ne_bot S (Ideal.ne_bot_of_height_eq_one h)
  apply le_antisymm
  · rw [← h, Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under S) P]
    exact le_self_add
  · exact Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hn)
#print axioms GKDivisor.heightOne_under
end GKDivisor
