module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! Actual determinant multiplication along a finite sequence of varying
Hilbert fibers. Every source/target change is a genuine continuous linear
equivalence, so equal dimension is proved rather than supplied. -/
public noncomputable section
namespace LeanShared.LinearEquivNormDetCocycle
open scoped BigOperators
variable {F : ℕ → Type*} [∀ n, NormedAddCommGroup (F n)]
  [∀ n, InnerProductSpace ℝ (F n)] [∀ n, FiniteDimensional ℝ (F n)]

@[expose] def product (a : ∀ n : ℕ, F n ≃L[ℝ] F (n + 1)) : ∀ n : ℕ, F 0 ≃L[ℝ] F n
  | 0 => ContinuousLinearEquiv.refl ℝ (F 0)
  | n + 1 => (product a n).trans (a n)

theorem normDet_product (a : ∀ n : ℕ, F n ≃L[ℝ] F (n + 1)) (n : ℕ) :
    (product a n).toLinearMap.normDet = ∏ j ∈ Finset.range n, (a j).toLinearMap.normDet := by
  induction n with
  | zero =>
    change (LinearMap.id : F 0 →ₗ[ℝ] F 0).normDet = 1
    exact LinearMap.normDet_id
  | succ n ih =>
    change ((a n).toLinearMap.comp (product a n).toLinearMap).normDet = _
    rw [LinearMap.normDet_comp_of_finrank_eq _ _ (product a n).toLinearEquiv.finrank_eq,
      ih, Finset.prod_range_succ, mul_comm]

end LeanShared.LinearEquivNormDetCocycle
