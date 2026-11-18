import ScalarMatrixActor
import FullG3
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Ring.Shrink
import Mathlib.Logic.Small.Set

noncomputable section
namespace G3Scalar
open Module

/-- Equality for the given family and a specified field embedding, even between
different universes. The source is the original algebra, not a presentation. -/
theorem finrank_family_map {k L : Type*} [Field k] [Field L] (f : k →+* L)
    {n : ℕ} {ι : Type*} (A : ι → Matrix (Fin n) (Fin n) k) :
    finrank k (Algebra.adjoin k (Set.range A)) =
      finrank L (Algebra.adjoin L (Set.range fun i => f.mapMatrix (A i))) := by
  let := f.toAlgebra
  have h := finrank_adjoin_map k L (Set.range A)
  rw [← Set.range_comp] at h
  exact h

/-- No closure hypothesis on the given field. This lemma interfaces directly
with the frozen theorem in Type, taking its own algebraic closure. -/
theorem charZero_small (k : Type) [Field k] [CharZero k] (n : ℕ)
    (A : Fin 3 → Matrix (Fin n) (Fin n) k) (hc : ∀ i j, Commute (A i) (A j)) :
    finrank k (Algebra.adjoin k (Set.range A)) ≤ n := by
  let f := algebraMap k (AlgebraicClosure k)
  rw [finrank_family_map f A]
  exact G3Assembly.matrix_triple_bound _ n _ fun i j => (hc i j).map f.mapMatrix

/-- Field expressions in a small number of generators. Used *only* to remove
the universe restriction of the original algebraically closed theorem. -/
private inductive Expr (ι : Type) where
  | atom (i : ι) | zero | one
  | add (a b : Expr ι) | mul (a b : Expr ι)
  | neg (a : Expr ι) | inv (a : Expr ι)

private def Expr.eval {ι : Type} {K : Type*} [Field K] (c : ι → K) : Expr ι → K
  | .atom i => c i | .zero => 0 | .one => 1
  | .add a b => a.eval c + b.eval c | .mul a b => a.eval c * b.eval c
  | .neg a => -a.eval c | .inv a => (a.eval c)⁻¹

private def coefficients {ι : Type} {K : Type*} [Field K] (c : ι → K) : Subfield K where
  carrier := Set.range (Expr.eval c)
  zero_mem' := ⟨.zero,rfl⟩
  one_mem' := ⟨.one,rfl⟩
  add_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨.add a b,rfl⟩
  mul_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨.mul a b,rfl⟩
  neg_mem' := by rintro _ ⟨a,rfl⟩; exact ⟨.neg a,rfl⟩
  inv_mem' := by rintro _ ⟨a,rfl⟩; exact ⟨.inv a,rfl⟩

/-- All sizes, all universes, over an arbitrary characteristic-zero field:
the only tuple hypothesis is pairwise commutation. -/
theorem charZero_triple_bound (K : Type*) [Field K] [CharZero K] (n : ℕ)
    (A : Fin 3 → Matrix (Fin n) (Fin n) K) (hc : ∀ i j, Commute (A i) (A j)) :
    finrank K (Algebra.adjoin K (Set.range A)) ≤ n := by
  let c : Fin 3 × Fin n × Fin n → K := fun p => A p.1 p.2.1 p.2.2
  let E := coefficients c
  let : Small.{0} E := inferInstanceAs (Small.{0} (Set.range (Expr.eval c)))
  let e : Shrink.{0} E ≃+* E := Shrink.ringEquiv E
  let f : Shrink.{0} E →+* K := E.subtype.comp e.toRingHom
  let : CharZero (Shrink.{0} E) := f.charZero
  let B : Fin 3 → Matrix (Fin n) (Fin n) (Shrink.{0} E) :=
    fun s i j => e.symm ⟨A s i j, Expr.atom (s,i,j), rfl⟩
  have mapped (i : Fin 3) : f.mapMatrix (B i) = A i := by
    ext x y
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hinj : Function.Injective (f.mapMatrix (m := Fin n)) := by
    intro M N h
    apply Matrix.ext
    intro i j
    exact f.injective (congrFun (congrFun h i) j)
  have comm (i j : Fin 3) : Commute (B i) (B j) := by
    apply hinj
    simpa only [map_mul,mapped] using (hc i j).eq
  have hdim := finrank_family_map f B
  have eqf : (fun i => f.mapMatrix (B i)) = A := funext mapped
  rw [eqf] at hdim
  rw [← hdim]
  exact charZero_small _ n B comm

/-- Literal three-named-matrix version, with no nonzero size assumption. -/
theorem charZero_three_matrices {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (X Y Z : Matrix (Fin n) (Fin n) K) (hxy : Commute X Y) (hxz : Commute X Z)
    (hyz : Commute Y Z) : finrank K (Algebra.adjoin K ({X,Y,Z} : Set _)) ≤ n := by
  let A : Fin 3 → Matrix (Fin n) (Fin n) K := ![X,Y,Z]
  have comm (i j : Fin 3) : Commute (A i) (A j) := by
    fin_cases i <;> fin_cases j <;>
      first | exact Commute.refl _ | exact hxy | exact hxz | exact hyz | exact hxy.symm | exact hxz.symm | exact hyz.symm
  have range : Set.range A = ({X,Y,Z} : Set _) := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩; fin_cases i <;> simp [A]
    · rintro (h|h|h)
      · exact ⟨0,h.symm⟩
      · exact ⟨1,h.symm⟩
      · exact ⟨2,(Set.mem_singleton_iff.mp h).symm⟩
  exact range ▸ charZero_triple_bound K n A comm

#print axioms finrank_family_map
#print axioms charZero_small
#print axioms charZero_triple_bound
#print axioms charZero_three_matrices
end G3Scalar
