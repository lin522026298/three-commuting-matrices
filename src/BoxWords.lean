import Mathlib.RingTheory.PowerBasis
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
noncomputable section
namespace DivisorG3
open Module Submodule Polynomial
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
abbrev box (x y : A) (m n : ℕ) := fun ij : Fin m × Fin n => x^ij.1.val * y^ij.2.val

variable [Nontrivial R]
theorem pow_reduce (x : A) (p : R[X]) (hp : p.Monic) (hx : aeval x p=0) (a : ℕ) :
    x^a ∈ span R (Set.range fun i : Fin p.natDegree => x^i.val) := by
  apply PowerBasis.mem_span_pow'.mpr
  refine ⟨X^a %ₘ p,(degree_modByMonic_lt _ hp).trans_le degree_le_natDegree,?_⟩
  rw [aeval_modByMonic_eq_self_of_root hx,map_pow,aeval_X]

/-- Only the pair on the quotient has to commute. The two presentation lifts need not. -/
theorem adjoin_box (x y : A) (h : Commute x y)
    (p q : R[X]) (hp : p.Monic) (hq : q.Monic) (hx : aeval x p=0) (hy : aeval y q=0) :
    (Algebra.adjoin R ({x,y} : Set A)).toSubmodule =
      span R (Set.range (box x y p.natDegree q.natDegree)) := by
  let L := span R (Set.range (box x y p.natDegree q.natDegree))
  have red (a b : ℕ) : x^a * y^b ∈ L := by
    have redL (i : Fin p.natDegree) (z : A) (hz : z ∈ span R (Set.range fun j : Fin q.natDegree => y^j.val)) : x^i.val*z ∈ L := by
      induction hz using Submodule.span_induction with
      | mem z hz => obtain ⟨j,rfl⟩ := hz; exact subset_span ⟨(i,j),rfl⟩
      | zero => simp
      | add _ _ _ _ hv hw => simpa [mul_add] using L.add_mem hv hw
      | smul c z _ hz => simpa [mul_smul_comm] using L.smul_mem c hz
    have hyb := pow_reduce y q hq hy b
    have hxa := pow_reduce x p hp hx a
    generalize x^a = v at hxa ⊢
    induction hxa using Submodule.span_induction with
    | mem z hz => obtain ⟨i,rfl⟩ := hz; exact redL i _ hyb
    | zero => simp
    | add _ _ _ _ hv hw => simpa [add_mul] using L.add_mem hv hw
    | smul c z _ hz => simpa [smul_mul_assoc] using L.smul_mem c hz
  let U : Submonoid A := {
    carrier := {a | ∃ m n : ℕ, a=x^m*y^n}
    one_mem' := ⟨0,0,by simp⟩
    mul_mem' := by
      rintro _ _ ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
      exact ⟨a+c,b+d,by
        rw [pow_add,pow_add,←mul_assoc, mul_assoc (x^a) (y^b) (x^c), ((h.pow_pow c b).symm).eq]
        simp only [mul_assoc]⟩ }
  have hU : Submonoid.closure ({x,y}:Set A) ≤ U := by
    apply Submonoid.closure_le.mpr
    rintro z (rfl | hz)
    · exact ⟨1,0,by simp⟩
    · obtain rfl := Set.mem_singleton_iff.mp hz; exact ⟨0,1,by simp⟩
  apply le_antisymm
  · rw [Algebra.adjoin_eq_span]
    exact span_le.mpr fun z hz => by obtain ⟨m,n,rfl⟩:=hU hz; exact red m n
  · apply span_le.mpr
    rintro _ ⟨⟨i,j⟩,rfl⟩
    exact (Algebra.adjoin R ({x,y}:Set A)).mul_mem
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) _)
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)) _)
#print axioms adjoin_box
end DivisorG3
