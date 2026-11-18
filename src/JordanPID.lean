import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section
open Module Polynomial
open scoped DirectSum
namespace ActualJordan
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [Module.Finite K M]

abbrev Tr (K : Type*) [Field K] (l : ℕ) := AdjoinRoot ((X : K[X])^l)

/-- Applied directly to the actual operator; the exponent-zero summands
returned by the PID theorem are allowed and later carry no basis vectors. -/
theorem exists_truncated_model (T : Module.End K M) (hn : IsNilpotent T) :
    ∃ (d : ℕ) (s : Fin d → ℕ) (e : M ≃ₗ[K] ((i : Fin d) → Tr K (s i))),
      ∀ (v : M) (i : Fin d), e (T v) i = AdjoinRoot.root ((X : K[X])^(s i)) * e v i := by
  classical
  have ht : Module.IsTorsion' (Module.AEval' T) (Submonoid.powers (X : K[X])) := by
    apply (Submodule.isTorsion'_powers_iff _).mpr
    obtain ⟨k,hk⟩ := hn
    intro v
    obtain ⟨v,rfl⟩ := (Module.AEval'.of T).surjective v
    exact ⟨k,by rw [Module.AEval'.X_pow_smul_of,hk,zero_smul,map_zero]⟩
  obtain ⟨d,s,⟨a⟩⟩ := Module.torsion_by_prime_power_decomposition
    (M:=Module.AEval' T) (Polynomial.irreducible_X (R:=K)) ht
  let f := a.trans (DFinsupp.linearEquivFunOnFintype)
  let e := (Module.AEval'.of T).trans (f.restrictScalars K)
  refine ⟨d,s,e,?_⟩
  intro v i
  change f (Module.AEval'.of T (T v)) i = _
  rw [← Module.AEval'.X_smul_of,map_smul]
  rfl
end ActualJordan
