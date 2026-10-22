module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The finite signed cancellation behind periodic fiber corrections.
For any permutation of a nonempty finite fiber, the alternating sum of
its principal minors vanishes because its permutation matrix fixes the
constant vector.  Removing the empty minor gives the literal coefficient
one of the signed nonempty-subset correction.
-/

public noncomputable section
namespace LeanShared.FinitePermutationMinorCancellation
open Matrix Finset
variable {F 𝕜 : Type*} [Fintype F] [DecidableEq F] [Field 𝕜]

theorem det_one_add_sum_principal (M : Matrix F F 𝕜) :
    (1 + M).det = ∑ s : Finset F, (M.submatrix (Subtype.val : s → F) Subtype.val).det := by
  let D := (detRowAlternating : (F → 𝕜) [⋀^F]→ₗ[𝕜] 𝕜)
  rw [add_comm]
  change D ((fun i => M i) + (fun i => (1 : Matrix F F 𝕜) i)) = _
  rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  exact det_piecewise_one_eq_submatrix_det M s

theorem det_one_sub_sum_principal (M : Matrix F F 𝕜) :
    (1 - M).det = ∑ s : Finset F,
      (-1 : 𝕜) ^ s.card * (M.submatrix (Subtype.val : s → F) Subtype.val).det := by
  simpa only [sub_eq_add_neg, Matrix.submatrix_neg, Pi.neg_apply, Matrix.det_neg, Fintype.card_coe]
    using det_one_add_sum_principal (-M)

theorem permutation_alternating_minors [Nonempty F] (P : Equiv.Perm F) :
    (∑ s : Finset F, (-1 : 𝕜) ^ s.card *
      ((P.permMatrix 𝕜).submatrix (Subtype.val : s → F) Subtype.val).det) = 0 := by
  rw [← det_one_sub_sum_principal]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro zero
    have atPoint := congrFun zero (Classical.arbitrary F)
    exact one_ne_zero atPoint
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.permMatrix_mulVec]
    exact sub_self _

theorem permutation_nonempty_signed_minors [Nonempty F] (P : Equiv.Perm F) :
    (∑ s ∈ (Finset.univ : Finset (Finset F)).erase ∅,
      -((-1 : 𝕜) ^ s.card *
        ((P.permMatrix 𝕜).submatrix (Subtype.val : s → F) Subtype.val).det)) = 1 := by
  have all := permutation_alternating_minors (𝕜 := 𝕜) P
  have split := Finset.sum_erase_add (Finset.univ : Finset (Finset F))
    (fun s => (-1 : 𝕜) ^ s.card *
      ((P.permMatrix 𝕜).submatrix (Subtype.val : s → F) Subtype.val).det) (Finset.mem_univ ∅)
  have emptyMinor : ((P.permMatrix 𝕜).submatrix
      (Subtype.val : (∅ : Finset F) → F) Subtype.val).det = 1 := Matrix.det_isEmpty
  rw [emptyMinor] at split
  simp only [Finset.card_empty, pow_zero, one_mul] at split
  rw [all] at split
  rw [Finset.sum_neg_distrib]
  exact neg_eq_iff_add_eq_zero.mpr split

end LeanShared.FinitePermutationMinorCancellation
