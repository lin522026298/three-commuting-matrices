module

public import Gerstenhaber.FourBlocks.MinimalSource.NilThreeSource

/-!
Choose a smallest counterexample inside the same class of nilpotent
commuting triples with a bounded first kernel.  The actual shorter-source
safety and the resulting socle budget are derived from that minimum.
This file does not exclude the selected counterexample.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u

namespace Gerstenhaber.FourBlocks.MinimalSource

open Module LinearMap

variable {K : Type u} [Field K]

/-- A failure of the original bound at literal dimension n. -/
def NilThreeCounterAt (K : Type u) [Field K] (k n : ℕ) : Prop :=
  ∃ X : FiniteNilTriple K,
    finrank K X.Carrier = n ∧ finrank K (LinearMap.ker (X.operator 0)) ≤ k ∧
      finrank K X.Carrier < finrank K (SourceAlgebra X)

/-- The minimum carries safety below its own dimension, for all actual
nilpotent triples in the same first-kernel class. -/
structure MinimalNilThreeCounter (K : Type u) [Field K] (k : ℕ) where
  source : FiniteNilTriple K
  block_bound : finrank K (LinearMap.ker (source.operator 0)) ≤ k
  failure : finrank K source.Carrier < finrank K (SourceAlgebra source)
  shorter_safe : NilThreeSafeBelow K (finrank K source.Carrier) k

/-- Every genuine failure has a minimum in the same restricted class.
In particular the smaller-module safety is not a new hard hypothesis. -/
theorem exists_minimal_nil_three_counter (k : ℕ)
    (hbad : ∃ X : FiniteNilTriple K,
      finrank K (LinearMap.ker (X.operator 0)) ≤ k ∧
        finrank K X.Carrier < finrank K (SourceAlgebra X)) :
    Nonempty (MinimalNilThreeCounter K k) := by
  classical
  have hex : ∃ n, NilThreeCounterAt K k n := by
    obtain ⟨X,hker,hX⟩ := hbad
    exact ⟨finrank K X.Carrier,X,rfl,hker,hX⟩
  obtain ⟨X,hXdim,hker,hX⟩ := Nat.find_spec hex
  refine ⟨⟨X,hker,hX,?_⟩⟩
  intro N _ _ _ Y hcomm hnil hlen hNker
  by_contra hfail
  have hNY : NilThreeCounterAt K k (finrank K N) := by
    refine ⟨FiniteNilTriple.of N Y hcomm hnil,rfl,hNker,?_⟩
    exact lt_of_not_ge hfail
  have hmin := Nat.find_min' hex hNY
  rw [← hXdim] at hmin
  omega

/-- Entry from an unbundled literal triple. Only the original commuting,
nilpotent, kernel-size and failed dimension hypotheses occur here. -/
theorem exists_minimal_counter_of_triple_failure
    (M : Type u) [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (Y : Fin 3 → Module.End K M) (hcomm : ∀ i j, Commute (Y i) (Y j))
    (hnil : ∀ i, IsNilpotent (Y i)) (k : ℕ)
    (hker : finrank K (LinearMap.ker (Y 0)) ≤ k)
    (hbad : finrank K M < finrank K (Algebra.adjoin K (Set.range Y))) :
    Nonempty (MinimalNilThreeCounter K k) :=
  exists_minimal_nil_three_counter k ⟨FiniteNilTriple.of M Y hcomm hnil,hker,hbad⟩

namespace MinimalNilThreeCounter

variable {k : ℕ} (X : MinimalNilThreeCounter K k)

instance carrier_nontrivial : Nontrivial X.source.Carrier :=
  sourceCarrier_nontrivial_of_failure X.source X.failure

def excess : ℕ := finrank K (SourceAlgebra X.source)-finrank K X.source.Carrier

theorem excess_pos : 0 < X.excess := by
  have h := X.failure
  change 0 < finrank K (SourceAlgebra X.source)-finrank K X.source.Carrier
  omega

theorem algebra_finrank_eq :
    finrank K (SourceAlgebra X.source) = finrank K X.source.Carrier+X.excess := by
  have h := X.failure
  change finrank K (SourceAlgebra X.source) =
    finrank K X.source.Carrier+(finrank K (SourceAlgebra X.source)-finrank K X.source.Carrier)
  omega

def augmentation : SourceAlgebra X.source →ₐ[K] K := sourceAugmentation X.source

theorem augmentation_nilpotent : IsNilpotent (augmentationIdeal X.augmentation) :=
  sourceAugmentation_nilpotent X.source

theorem augmentation_first_root : X.augmentation (sourceRoot X.source 0) = 0 :=
  sourceAugmentation_root X.source 0

/-- Both actual families and the two-fiber budget now follow without
assuming any annihilator equality, injection or shorter-source budget. -/
theorem socle_budget [Infinite K] :
    X.excess+1 ≤ finrank K (Top (M := X.source.Carrier) X.augmentation) ∧
      X.excess+1 ≤ finrank K (moduleSocle (M := X.source.Carrier) X.augmentation) ∧
      (X.excess+1)*(finrank K (Top (M := X.source.Carrier) X.augmentation)+
        finrank K (moduleSocle (M := X.source.Carrier) X.augmentation)-(X.excess+1)) ≤
        finrank K (algebraSocle X.augmentation) := by
  exact actual_socle_budget_of_nilThreeSafeBelow
    (sourceRoot X.source) (sourceRoot_nilpotent X.source)
    (sourceRoot_adjoin_eq_top X.source) k X.excess X.algebra_finrank_eq
    (by rw [sourceRoot_lsmul]; exact X.block_bound) X.shorter_safe

theorem top_finrank_le_blocks :
    finrank K (Top (M := X.source.Carrier) X.augmentation) ≤ k := by
  exact (top_finrank_le_t_kernel X.augmentation (sourceRoot X.source 0)
    X.augmentation_first_root).trans (by
      rw [sourceRoot_lsmul]; exact X.block_bound)

theorem socle_finrank_le_blocks :
    finrank K (moduleSocle (M := X.source.Carrier) X.augmentation) ≤ k := by
  exact (socle_finrank_le_t_kernel X.augmentation (sourceRoot X.source 0)
    X.augmentation_first_root).trans (by
      rw [sourceRoot_lsmul]; exact X.block_bound)

theorem excess_lt_blocks [Infinite K] : X.excess < k := by
  have hbudget := X.socle_budget
  have htop := X.top_finrank_le_blocks
  omega

/-- The usual two-fiber lower bound is derived from the full
excess-dependent bound, rather than supplied as a source assumption. -/
theorem socle_budget_two [Infinite K] :
    2*(finrank K (Top (M := X.source.Carrier) X.augmentation)+
      finrank K (moduleSocle (M := X.source.Carrier) X.augmentation)-2) ≤
        finrank K (algebraSocle X.augmentation) := by
  have hb := X.socle_budget
  have he := X.excess_pos
  set a := finrank K (Top (M := X.source.Carrier) X.augmentation) with ha
  set b := finrank K (moduleSocle (M := X.source.Carrier) X.augmentation) with hb'
  set c := X.excess+1 with hc
  have hca : c ≤ a := hb.1
  have hcb : c ≤ b := hb.2.1
  have htwo : 2 ≤ c := by omega
  have hsum : (a+b-c)+c = a+b := Nat.sub_add_cancel (by omega)
  have hd : 2 ≤ a+b-c := by omega
  have hd' : (a+b-c-2)+2 = a+b-c := Nat.sub_add_cancel hd
  have hc' : (c-2)+2=c := Nat.sub_add_cancel htwo
  have hab : (a+b-2)+2=a+b := Nat.sub_add_cancel (by omega)
  have hnonneg : 0 ≤ (c-2)*(a+b-c-2) := Nat.zero_le _
  change 2*(a+b-2) ≤ _
  have hbound : c*(a+b-c) ≤ finrank K (algebraSocle X.augmentation) := hb.2.2
  nlinarith

/-- At top dimension at most two, minimum-counterexample geometry
forces excess one and the full actual socle action. -/
theorem full_socle_action_of_top_le_two [Infinite K]
    (htop : finrank K (Top (M := X.source.Carrier) X.augmentation) ≤ 2) :
    X.excess = 1 ∧ finrank K (Top (M := X.source.Carrier) X.augmentation) = 2 ∧
      Function.Bijective (socleAction (M := X.source.Carrier) X.augmentation) := by
  have hb := X.socle_budget
  have he := X.excess_pos
  have heq : X.excess=1 := by omega
  have ha : finrank K (Top (M := X.source.Carrier) X.augmentation)=2 := by omega
  refine ⟨heq,ha,?_⟩
  apply socleAction_bijective_of_finrank_eq X.augmentation
  apply le_antisymm
  · exact algebraSocle_finrank_le_product X.augmentation
  · have htwo := X.socle_budget_two
    rw [ha] at htwo ⊢
    omega

end MinimalNilThreeCounter

end Gerstenhaber.FourBlocks.MinimalSource
