module

public import LeanShared.Analysis.StableRangeInverse

/-! The actual operator blocks of a topological Fitting decomposition:
a nilpotent block and a continuously invertible block. -/

public section
open ContinuousLinearMap Submodule
namespace LeanShared.FittingBlocks
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A stable Fitting splitting gives actual nilpotent/invertible blocks and
an exact continuous conjugation identity for the original operator. -/
theorem exists_blocks (S : E →L[ℂ] E) (n : ℕ)
    (hcompl : IsTopCompl (S ^ n).ker (S ^ n).range)
    (hker : (S ^ (n + 1)).ker = (S ^ n).ker)
    (hrange : (S ^ (n + 1)).range = (S ^ n).range) :
    ∃ (N : (S ^ n).ker →L[ℂ] (S ^ n).ker)
      (B : (S ^ n).range →L[ℂ] (S ^ n).range),
      N ^ n = 0 ∧ IsUnit B ∧
      ((S ^ n).ker.prodEquivOfIsTopCompl (S ^ n).range hcompl).conjContinuousAlgEquiv
        (N.prodMap B) = S := by
  let K := (S ^ n).ker
  let V := (S ^ n).range
  let : CompleteSpace V := hcompl.isClosed'.isComplete.completeSpace_coe
  have invariant : ∀ x ∈ K, S x ∈ K := by
    intro x hx
    change (S ^ n) x = 0 at hx
    change (S ^ n) (S x) = 0
    rw [← mul_apply_eq_comp, ← pow_succ, pow_succ', mul_apply_eq_comp, hx, map_zero]
  let N : K →L[ℂ] K := S.restrict invariant
  have powers (k : ℕ) (x : K) : ((N ^ k) x).val = (S ^ k) x.val := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, pow_succ', mul_apply_eq_comp]
      change S (((N ^ k) x).val) = S ((S ^ k) x.val)
      rw [ih]
  have nilpotent : N ^ n = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change ((N ^ n) x).val = 0
    rw [powers]
    exact x.property
  obtain ⟨e, he⟩ := StableRangeInverse.exists_equiv S n hcompl hker hrange
  let B : V →L[ℂ] V := e.toContinuousLinearMap
  let equivalence := K.prodEquivOfIsTopCompl V hcompl
  refine ⟨N, B, nilpotent, ContinuousLinearMap.isUnit_iff_bijective.mpr e.bijective, ?_⟩
  ext x
  let kv := equivalence.symm x
  have decomposition : kv.1.val + kv.2.val = x := equivalence.apply_symm_apply x
  change (N kv.1).val + (e kv.2).val = S x
  change S kv.1.val + (e kv.2).val = S x
  rw [he, ← map_add, decomposition]

end LeanShared.FittingBlocks
