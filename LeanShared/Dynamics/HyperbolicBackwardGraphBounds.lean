module
public import LeanShared.Dynamics.HyperbolicBackwardGraph

/-! A uniform bound for the actual nonlinear unstable graph and its complete
backward orbit. The expanding coordinate is prescribed at time zero; its size
is not spuriously multiplied by the reciprocal contraction margin. This bound
makes the global graph construction usable inside a genuine local collar. -/
public noncomputable section
namespace LeanShared.HyperbolicBackwardGraph
open scoped NNReal BoundedContinuousFunction

private theorem raw_norm_parameter {U S : Type*} [NormedAddCommGroup U]
    [NormedAddCommGroup S] (A : ℕ → U → U) (B : ℕ → S → S)
    (N : ℕ → U × S → U × S) (u : U) (z : ℕ → U × S) (n : ℕ) :
    ‖HyperbolicBackwardTransform.raw A B N u z n‖ ≤
      max ‖u‖ ‖HyperbolicBackwardTransform.raw A B N 0 z n‖ := by
  cases n with
  | zero => simp only [HyperbolicBackwardTransform.raw, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg _), le_refl]
  | succ n => exact le_max_right _ _

namespace Data

theorem transform_norm_bound {U S : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup S] [NormedSpace ℝ S]
    (d : Data U S) (u : U) (z : ℕ →ᵇ U × S) :
    ‖d.transform u z‖ ≤ max ‖u‖
      (((d.k + d.δ : ℝ≥0) : ℝ) * ‖z‖ + ((d.k : ℝ) + 1) * d.zero_bound) := by
  let C : ℝ := ((d.k : ℝ) + 1) * d.zero_bound
  have nonnegative : 0 ≤ C := mul_nonneg (by positivity)
    ((norm_nonneg _).trans (d.nonlinear_zero 0))
  apply (BoundedContinuousFunction.norm_le
    ((norm_nonneg u).trans (le_max_left _ _))).mpr
  intro n
  have estimate := HyperbolicBackwardTransform.raw_distance
    (fun i => (d.expanding i).symm) (fun i => d.contracting i) d.nonlinear
    d.k d.δ d.k_le_one d.inverse_bound d.stable_bound d.nonlinear_bound 0 z
    (fun _ => 0) ‖z‖
    (fun i => by simpa only [dist_zero_right] using z.norm_coe_le_norm i) n
  have at_zero := HyperbolicBackwardTransform.raw_zero_bound
    (fun i => (d.expanding i).symm) (fun i => d.contracting i) d.nonlinear d.k
    d.inverse_bound (fun i => (d.expanding i).symm.map_zero)
    (fun i => (d.contracting i).map_zero) d.zero_bound d.nonlinear_zero 0 n
  change _ ≤ max ‖(0 : U)‖ C at at_zero
  rw [norm_zero, max_eq_right nonnegative] at at_zero
  have bound : ‖HyperbolicBackwardTransform.raw (fun i => (d.expanding i).symm)
      (fun i => d.contracting i) d.nonlinear 0 z n‖ ≤
      ((d.k + d.δ : ℝ≥0) : ℝ) * ‖z‖ + C := by
    have triangle := dist_triangle
      (HyperbolicBackwardTransform.raw (fun i => (d.expanding i).symm)
        (fun i => d.contracting i) d.nonlinear 0 z n)
      (HyperbolicBackwardTransform.raw (fun i => (d.expanding i).symm)
        (fun i => d.contracting i) d.nonlinear 0 (fun _ => 0) n) 0
    simp only [dist_zero_right] at triangle
    exact triangle.trans (add_le_add estimate at_zero)
  exact (raw_norm_parameter _ _ _ u z n).trans (max_le_max le_rfl bound)

theorem orbit_norm_bound {U S : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (d : Data U S) (u : U) :
    ‖d.orbit u‖ ≤ max ‖u‖
      ((((d.k : ℝ) + 1) * d.zero_bound) / (1 - (d.k + d.δ : ℝ≥0))) := by
  have fixed := (d.transform_contracting u).fixedPoint_isFixedPt
  have estimate := d.transform_norm_bound u (d.orbit u)
  change d.transform u (d.orbit u) = d.orbit u at fixed
  rw [fixed] at estimate
  rcases le_max_iff.mp estimate with small | forced
  · exact small.trans (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ (d.transform_contracting u).one_sub_K_pos).mpr
    nlinarith

theorem orbit_norm_lt {U S : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (d : Data U S) (u : U) (R : ℝ) (initial : ‖u‖ < R)
    (forcing : ((d.k : ℝ) + 1) * d.zero_bound <
      (1 - (d.k + d.δ : ℝ≥0)) * R) : ‖d.orbit u‖ < R := by
  apply (d.orbit_norm_bound u).trans_lt
  apply max_lt initial
  exact (div_lt_iff₀ (d.transform_contracting u).one_sub_K_pos).mpr
    (by simpa only [mul_comm] using forcing)

end Data
end LeanShared.HyperbolicBackwardGraph
