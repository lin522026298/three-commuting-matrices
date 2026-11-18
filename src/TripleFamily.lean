import OriginActor
import Mathlib.Data.Fin.VecNotation
noncomputable section
namespace DivisorG3
open Module LinearMap
variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
def triples (t y z : End k W) : Fin 3 → End k W := ![t,y,z]
theorem family_adjoin (S : Fin 3 → End k W) : Algebra.adjoin k (Set.range S)=triple (S 0) (S 1) (S 2) := by
  congr 1
  ext v
  constructor
  · rintro ⟨i,rfl⟩; fin_cases i <;> simp
  · rintro (h|h|h)
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,(Set.mem_singleton_iff.mp h).symm⟩
theorem triples_comm {t y z : End k W} (hy : Commute t y) (hz : Commute t z) (hp : Commute y z) :
    ∀ i j, Commute (triples t y z i) (triples t y z j) := by
  intro i j; fin_cases i <;> fin_cases j <;>
    first | exact Commute.refl _ | exact hy | exact hz | exact hp | exact hy.symm | exact hz.symm | exact hp.symm
#print axioms family_adjoin
#print axioms triples_comm
end DivisorG3
