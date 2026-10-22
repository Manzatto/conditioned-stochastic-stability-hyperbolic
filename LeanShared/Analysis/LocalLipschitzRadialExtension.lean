module
public import LeanShared.Analysis.RadialBallRetraction
public import Mathlib.Analysis.Calculus.MeanValue

/-! A constructive continuous-family extension of locally small nonlinear
maps. Retraction onto the actual closed ball preserves the original map there
and costs at most a factor two in its Lipschitz bound. Local derivative bounds
supply that bound by the mean value theorem. -/
public noncomputable section
namespace LeanShared.RadialBallRetraction
open Set
open scoped NNReal

@[expose] def extend {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (f : E → F) : E → F := f ∘ retract R

theorem extend_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) (positive : 0 < R) (f : E → F) {x : E} (inside : ‖x‖ ≤ R) :
    extend R f x = f x := by rw [extend, Function.comp_apply, retract_eq_self R positive inside]

theorem lipschitz_extend {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [PseudoMetricSpace F] (R : ℝ) (positive : 0 < R) (f : E → F) (k : ℝ≥0)
    (local_bound : LipschitzOnWith k f (Metric.closedBall 0 R)) :
    LipschitzWith (k * 2) (extend R f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have inside (z : E) : retract R z ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Function.comp_def] using norm_retract_le R positive z
  calc
    _ ≤ k * dist (retract R x) (retract R y) := local_bound.dist_le_mul _ (inside x) _ (inside y)
    _ ≤ (k : ℝ) * (2 * dist x y) := mul_le_mul_of_nonneg_left
      ((lipschitz_retract R positive).dist_le_mul x y) k.coe_nonneg
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat, mul_assoc]

theorem lipschitz_extend_of_fderiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : ℝ) (positive : 0 < R) (f : E → F) (k : ℝ≥0)
    (differentiable : ∀ x ∈ Metric.closedBall 0 R, DifferentiableAt ℝ f x)
    (bound : ∀ x ∈ Metric.closedBall 0 R, ‖fderiv ℝ f x‖ ≤ (k : ℝ)) :
    LipschitzWith (k * 2) (extend R f) :=
  lipschitz_extend R positive f k (Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    differentiable (fun x hx => NNReal.coe_le_coe.mp (bound x hx)) (convex_closedBall 0 R))

theorem continuous_extend_family {P E F : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace F]
    (R : ℝ) (positive : 0 < R) (f : P × E → F)
    (continuous : ContinuousOn f (univ ×ˢ Metric.closedBall 0 R)) :
    Continuous (fun z : P × E => extend R (fun x => f (z.1, x)) z.2) := by
  apply continuous.comp_continuous
    (continuous_fst.prodMk ((lipschitz_retract R positive).continuous.comp continuous_snd))
  intro z
  refine ⟨mem_univ _, ?_⟩
  simpa only [Metric.mem_closedBall, dist_zero_right, Function.comp_def] using norm_retract_le R positive z.2

end LeanShared.RadialBallRetraction
