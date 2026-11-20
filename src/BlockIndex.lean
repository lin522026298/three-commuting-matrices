module

public import IntrinsicDVR
public import DividedTail
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section
noncomputable section
namespace DivisorG3
open Module LinearMap Submodule Matrix IsDiscreteValuationRing
open scoped Matrix
variable {R ι β : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
abbrev QP (P : Matrix ι ι R) := Coker P.mulVecLin
def diagP (P : Matrix ι ι R) := blockDiagonal fun _ : ι => P
def columnMap (P : Matrix ι ι R) : ((ι×ι)→R) →ₗ[R] (ι → QP P) where
  toFun v j := P.mulVecLin.range.mkQ (fun i => v (i,j))
  map_add' _ _ := by ext; apply map_add
  map_smul' c v := by funext j; exact P.mulVecLin.range.mkQ.map_smul c (fun i => v (i,j))

omit [DecidableEq ι] in
theorem column_surj (P : Matrix ι ι R) : Function.Surjective (columnMap P) := by
  intro z
  choose v hv using fun j => P.mulVecLin.range.mkQ_surjective (z j)
  exact ⟨fun a => v a.2 a.1,funext hv⟩

theorem diag_apply (P : Matrix ι ι R) (w : (ι×ι)→R) (i j : ι) :
    (diagP P).mulVecLin w (i,j) = (P.mulVecLin (fun a => w (a,j))) i := by
  classical
  simp [diagP,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply,ite_mul]

theorem column_ker (P : Matrix ι ι R) : (columnMap P).ker = matrixColumnLattice (diagP P) := by
  ext v
  constructor
  · intro hv
    have hv' (j : ι) : (fun i => v (i,j)) ∈ P.mulVecLin.range :=
      (Quotient.mk_eq_zero _).mp (congrFun (show columnMap P v=0 from hv) j)
    choose w hw using hv'
    exact ⟨fun a => w a.2 a.1,funext fun ⟨i,j⟩ => (diag_apply P _ i j).trans (congrFun (hw j) i)⟩
  · rintro ⟨w,rfl⟩
    change columnMap P _ = 0
    funext j
    apply (Quotient.mk_eq_zero _).mpr
    exact ⟨fun i => w (i,j),funext fun i => (diag_apply P _ i j).symm⟩

def blockColumns (P : Matrix ι ι R) (B : β → Matrix ι ι R) : Matrix (ι×ι) ((ι×ι)⊕β) R :=
  fromCols (diagP P) (fun ij l => B l ij.1 ij.2)
def wordImage (P : Matrix ι ι R) (B : β → Matrix ι ι R) : Submodule R (ι → QP P) :=
  span R (Set.range fun l : β => fun j => P.mulVecLin.range.mkQ ((B l).col j))

omit [DecidableEq β] in
theorem block_ker_le (P : Matrix ι ι R) (B : β → Matrix ι ι R) :
    (columnMap P).ker ≤ matrixColumnLattice (blockColumns P B) := by
  rw [column_ker]
  change (diagP P).mulVecLin.range ≤ (blockColumns P B).mulVecLin.range
  rw [Matrix.range_mulVecLin,Matrix.range_mulVecLin]
  exact Submodule.span_mono fun _ ⟨ij,e⟩ => ⟨.inl ij,e⟩

omit [DecidableEq β] in
theorem block_image (P : Matrix ι ι R) (B : β → Matrix ι ι R) :
    (matrixColumnLattice (blockColumns P B)).map (columnMap P) = wordImage P B := by
  rw [matrixColumnLattice,Matrix.range_mulVecLin (blockColumns P B),Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨ij,rfl⟩,rfl⟩
    cases ij with
    | inl j =>
      have hz : (diagP P).col j ∈ (columnMap P).ker := by
        rw [column_ker,matrixColumnLattice,Matrix.range_mulVecLin (diagP P)]
        exact subset_span ⟨j,rfl⟩
      exact (show columnMap P ((diagP P).col j)=0 from hz) ▸ zero_mem _
    | inr l => exact subset_span ⟨l,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨l,rfl⟩
    exact subset_span ⟨_,⟨Sum.inr l,rfl⟩,rfl⟩

def blockQuotEquiv (P : Matrix ι ι R) (B : β → Matrix ι ι R) :
    colQuot (blockColumns P B) ≃ₗ[R] (ι → QP P) ⧸ wordImage P B := by
  let f := columnMap P
  let L := matrixColumnLattice (blockColumns P B)
  let N := wordImage P B
  let g := N.mkQ.comp f
  have h : g.ker=L := by
    rw [ker_comp,ker_mkQ]; dsimp only [N,L,f]; rw [←block_image P B,Submodule.comap_map_eq,sup_eq_left.mpr (block_ker_le P B)]
  exact (Submodule.quotEquivOfEq _ _ h.symm) ≪≫ₗ g.quotKerEquivOfSurjective (N.mkQ_surjective.comp (column_surj P))

variable {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
omit [Fintype β] [DecidableEq β] in
theorem block_minor_nonzero (P : Matrix ι ι V) (hp : P.det≠0) (B : β → Matrix ι ι V) :
    ((blockColumns P B).submatrix _root_.id Sum.inl).det ≠ 0 := by
  change (blockDiagonal (fun _ : ι => P)).det≠0
  rw [det_blockDiagonal]; exact Finset.prod_ne_zero_iff.mpr fun _ _ => hp

theorem block_index (P : Matrix ι ι V) (hp : P.det≠0) (B : β → Matrix ι ι V) :
    length V (V ⧸ allColumnMinorIdeal (blockColumns P B)) + length V (wordImage P B) =
      Fintype.card ι * length V (QP P) := by
  rw [(intrinsic_colength _ _ (block_minor_nonzero P hp B)).1,(blockQuotEquiv P B).length_eq]
  have e := length_eq_add_of_exact (wordImage P B).subtype (wordImage P B).mkQ
    (wordImage P B).subtype_injective (wordImage P B).mkQ_surjective
    (LinearMap.exact_subtype_mkQ _)
  rw [add_comm,← e,Module.length_pi_of_fintype]
  simp

#print axioms column_ker
#print axioms blockQuotEquiv
#print axioms block_index
end DivisorG3
