module

public import LeanShared.Analysis.GraphBlockPerturbation
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The actual unstable principal block of a chronological word factors
through its successive graph blocks. Its determinant therefore accumulates
only the per-step relative loss, without a cost for the number of charts. -/
public noncomputable section
namespace LeanShared.GraphBlockJacobianProduct
variable {E U S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

@[expose] def product (L : ℕ → E →L[ℝ] E) : ℕ → E →L[ℝ] E
  | 0 => ContinuousLinearMap.id ℝ E
  | n + 1 => (L n).comp (product L n)

theorem intertwines (L : ℕ → U × S →L[ℝ] U × S) (G : ℕ → U →L[ℝ] S)
    (A : ℕ → U →L[ℝ] U)
    (step : ∀ n, (L n).comp (GraphBlockPerturbation.graph (G n)) =
      (GraphBlockPerturbation.graph (G (n + 1))).comp (A n)) (n : ℕ) :
    (product L n).comp (GraphBlockPerturbation.graph (G 0)) =
      (GraphBlockPerturbation.graph (G n)).comp (product A n) := by
  induction n with
  | zero => ext v <;> rfl
  | succ n ih =>
    rw [product, ContinuousLinearMap.comp_assoc, ih, ← ContinuousLinearMap.comp_assoc,
      step, ContinuousLinearMap.comp_assoc]
    rfl

theorem principal_eq (L : ℕ → U × S →L[ℝ] U × S) (G : ℕ → U →L[ℝ] S)
    (A : ℕ → U →L[ℝ] U) (initial : G 0 = 0)
    (step : ∀ n, (L n).comp (GraphBlockPerturbation.graph (G n)) =
      (GraphBlockPerturbation.graph (G (n + 1))).comp (A n)) (n : ℕ) :
    (ContinuousLinearMap.fst ℝ U S).comp
      ((product L n).comp (ContinuousLinearMap.inl ℝ U S)) = product A n := by
  have action := intertwines L G A step n
  ext v
  have same := congrArg (fun F : U →L[ℝ] U × S => (F v).1) action
  change ((product L n) (v, 0)).1 = (product A n) v
  simpa only [ContinuousLinearMap.comp_apply, GraphBlockPerturbation.graph,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, initial, zero_apply] using same

theorem determinant_product (A : ℕ → U →L[ℝ] U) (n : ℕ) :
    |(product A n).toLinearMap.det| = ∏ i ∈ Finset.range n, |(A i).toLinearMap.det| := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty]
    change |(LinearMap.id : U →ₗ[ℝ] U).det| = 1
    rw [LinearMap.det_id, abs_one]
  | succ n ih =>
    simp only [product, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, abs_mul,
      Finset.prod_range_succ, ih]
    exact mul_comm _ _

end LeanShared.GraphBlockJacobianProduct
