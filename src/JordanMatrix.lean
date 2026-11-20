module

public import JordanNilTest

@[expose] public section

/-! Literal field-matrix interface.  The block index is h (length h+1), p is
the level above the socle, and a numbers the strings of that length. -/
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)

abbrev Ix := (h : Fin H) × ((_p : Fin (h.val+1)) × Fin (m h))

def coordBasis : Basis (Ix m) K (V K m) :=
  Pi.basis fun h => Pi.basis fun _ => Pi.basisFun K (Fin (m h))

theorem coord_repr (v : V K m) (h : Fin H) (p : Fin (h.val+1)) (a : Fin (m h)) :
    (coordBasis m).repr v ⟨h,p,a⟩ = v h p a := by
  simp [coordBasis,Pi.basis_repr,Pi.basisFun_repr]

theorem coord_apply (h : Fin H) (p : Fin (h.val+1)) (a : Fin (m h)) :
    (coordBasis (K:=K) m) ⟨h,p,a⟩ = Pi.single h (Pi.single p (Pi.single a 1)) := by
  simp [coordBasis,Pi.basis_apply,Pi.basisFun_apply]

def matrixJ := LinearMap.toMatrixAlgEquiv (coordBasis (K:=K) m) (J m)

theorem matrixJ_apply (h : Fin H) (p q : Fin (h.val+1)) (a b : Fin (m h)) :
    matrixJ (K:=K) m ⟨h,p,a⟩ ⟨h,q,b⟩ =
      if p.val+1=q.val ∧ a=b then 1 else 0 := by
  rw [matrixJ,LinearMap.toMatrixAlgEquiv_apply,coord_repr,coord_apply]
  change (if hc : p.val+1 < h.val+1 then
    (Pi.single h (Pi.single q (Pi.single b (1:K))) : V K m) h ⟨p.val+1,hc⟩ else 0) a = _
  by_cases hs : p.val+1=q.val
  · have hq : q.val ≤ h.val := Nat.le_of_lt_succ q.isLt
    simp [hs,hq,Pi.single_apply]
  · by_cases hh : p.val+1<h.val+1
    · have hn : (⟨p.val+1,hh⟩ : Fin (h.val+1)) ≠ q := fun e => hs (congrArg Fin.val e)
      simp [hh,hs,Pi.single_eq_of_ne hn]
    · simp [hh,hs]

theorem matrixJ_other (h l : Fin H) (p : Fin (h.val+1)) (q : Fin (l.val+1))
    (a : Fin (m h)) (b : Fin (m l)) (hh : h≠l) :
    matrixJ (K:=K) m ⟨h,p,a⟩ ⟨l,q,b⟩ = 0 := by
  rw [matrixJ,LinearMap.toMatrixAlgEquiv_apply,coord_repr,coord_apply]
  change (if hc : p.val+1 < h.val+1 then
    (Pi.single l (Pi.single q (Pi.single b (1:K))) : V K m) h ⟨p.val+1,hc⟩ else 0) a = 0
  split <;> simp [Pi.single_eq_of_ne hh]

def rawBlock (Z : Matrix (Ix m) (Ix m) K) (h : Fin H) : Matrix (Fin (m h)) (Fin (m h)) K :=
  fun a b => Z ⟨h,0,a⟩ ⟨h,0,b⟩

def Bmat (K : Type*) {H : ℕ} (m : Fin H → ℕ) :=
  (h : Fin H) → Matrix (Fin (m h)) (Fin (m h)) K

theorem block_entry (z : Cent (K:=K) m) (h : Fin H) :
    LinearMap.toMatrixAlgEquiv (Pi.basisFun K (Fin (m h))) (part m z h) =
      rawBlock m (LinearMap.toMatrixAlgEquiv (coordBasis m) z.1) h := by
  ext a b
  rw [LinearMap.toMatrixAlgEquiv_apply,Pi.basisFun_repr,
      Pi.basisFun_apply]
  change z.1 (put m h (Pi.single b 1)) h 0 a = _
  rw [rawBlock,LinearMap.toMatrixAlgEquiv_apply,coord_repr,coord_apply]
  rfl

/-- Input hypothesis is the true square matrix commutation with the literal Jordan matrix. -/
def decode (Z : Matrix (Ix m) (Ix m) K) (hZ : Commute Z (matrixJ m)) : Cent (K:=K) m := by
  let e := LinearMap.toMatrixAlgEquiv (coordBasis (K:=K) m)
  refine ⟨e.symm Z, (Subalgebra.mem_centralizer_iff K).mpr ?_⟩
  rintro _ ⟨rfl⟩
  apply e.injective
  simpa [e,matrixJ] using hZ.eq.symm

@[simp] theorem encode_decode (Z : Matrix (Ix m) (Ix m) K) (hZ : Commute Z (matrixJ m)) :
    LinearMap.toMatrixAlgEquiv (coordBasis (K:=K) m) (decode m Z hZ).1 = Z :=
  AlgEquiv.apply_symm_apply _ _

theorem matrix_block_nilpotent_iff (Z : Matrix (Ix m) (Ix m) K)
    (hZ : Commute Z (matrixJ m)) :
    IsNilpotent Z ↔ ∀ h, IsNilpotent (rawBlock m Z h) := by
  let z := decode m Z hZ
  have htrans : IsNilpotent Z ↔ IsNilpotent z.1 := by
    rw [← encode_decode m Z hZ]
    exact IsNilpotent.map_iff (LinearMap.toMatrixAlgEquiv (coordBasis (K:=K) m)).injective
  rw [htrans,nilpotent_iff_blocks]
  apply forall_congr'
  intro h
  have e := block_entry m z h
  rw [show (LinearMap.toMatrixAlgEquiv (coordBasis m)) z.1=Z from encode_decode m Z hZ] at e
  rw [← e]
  exact (IsNilpotent.map_iff (LinearMap.toMatrixAlgEquiv (Pi.basisFun K (Fin (m h)))).injective).symm

/-- One genuine commuting Z simultaneously realizes every tuple of square matrices. -/
theorem rawBlock_surjective (Q : Bmat K m) :
    ∃ Z : Matrix (Ix m) (Ix m) K, Commute Z (matrixJ m) ∧ ∀ h, rawBlock m Z h = Q h := by
  let f : B K m := fun h => (LinearMap.toMatrixAlgEquiv (Pi.basisFun K _)).symm (Q h)
  let z := sectionHom m f
  let e := LinearMap.toMatrixAlgEquiv (coordBasis (K:=K) m)
  refine ⟨e z.1,(commJ m z).map e.toAlgHom,?_⟩
  intro h
  rw [← block_entry]
  have hs : part m z h = f h := congrFun (primitive_section m f) h
  rw [hs]
  exact AlgEquiv.apply_symm_apply _ _

end JordanPrimitive
