module
public import LeanShared.Dynamics.HyperbolicShadowing
public import LeanShared.Analysis.LocalLipschitzRadialExtension
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Tactic.Abel

/-! Actual local hyperbolic maps have no nonzero small entire orbit through
the zero reference orbit. The nonlinear extension and bilateral contraction
are constructed from local differential bounds, not supplied as sources. -/
public noncomputable section
namespace LeanShared.LocalHyperbolicOrbitUniqueness
open Set
open scoped NNReal BoundedContinuousFunction

set_option maxHeartbeats 1600000 in
theorem eq_zero
    {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (H : ℤ → U × S → U × S) (A : ℤ → U ≃L[ℝ] U) (B : ℤ → S →L[ℝ] S)
    (k δ : ℝ≥0) (small : k + δ * 2 < 1)
    (inverse : ∀ n, ‖(A n).symm.toContinuousLinearMap‖ ≤ (k : ℝ))
    (stable : ∀ n, ‖B n‖ ≤ (k : ℝ))
    (R : ℝ) (positive : 0 < R)
    (differentiable : ∀ n z, ‖z‖ ≤ R → DifferentiableAt ℝ (H n) z)
    (derivative : ∀ n z, ‖z‖ ≤ R →
      ‖fderiv ℝ (H n) z - (A n).toContinuousLinearMap.prodMap (B n)‖ ≤ (δ : ℝ))
    (origin : ∀ n, H n 0 = 0)
    (z : ℤ → U × S) (bounded : ∀ n, ‖z n‖ ≤ R)
    (step : ∀ n, H n (z (n + 1)) = z n) : ∀ n, z n = 0 := by
  let block := fun n => (A n).toContinuousLinearMap.prodMap (B n)
  let remainder := fun n w => H n w - block n w
  have remainder_diff (n : ℤ) (w : U × S) (hw : ‖w‖ ≤ R) :
      DifferentiableAt ℝ (remainder n) w :=
    (differentiable n w hw).sub (block n).differentiableAt
  have remainder_bound (n : ℤ) (w : U × S) (hw : ‖w‖ ≤ R) :
      ‖fderiv ℝ (remainder n) w‖ ≤ (δ : ℝ) := by
    have expression : remainder n = H n - ⇑(block n) := by funext v; rfl
    rw [expression, fderiv_sub (differentiable n w hw) (block n).differentiableAt,
      (block n).fderiv]
    exact derivative n w hw
  let d : HyperbolicShadowing.Data U S := {
    expanding := A
    contracting := B
    nonlinear := fun n => RadialBallRetraction.extend R (remainder n)
    k := k
    δ := δ * 2
    small := small
    inverse_bound := fun n => ContinuousLinearMap.lipschitzWith_of_opNorm_le (inverse n)
    stable_bound := fun n => ContinuousLinearMap.lipschitzWith_of_opNorm_le (stable n)
    nonlinear_bound := fun n => RadialBallRetraction.lipschitz_extend_of_fderiv
      R positive (remainder n) δ
      (fun w hw => remainder_diff n w (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw))
      (fun w hw => remainder_bound n w (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw))
    error := 0
    nonlinear_zero := fun n => by
      rw [RadialBallRetraction.extend_eq R positive (remainder n) (by simpa only [norm_zero] using positive.le)]
      simp only [remainder, origin, map_zero, sub_self, norm_zero, le_refl]
  }
  have agreement (n : ℤ) (w : U × S) (hw : ‖w‖ ≤ R) : d.map n w = H n w := by
    have same := RadialBallRetraction.extend_eq R positive (remainder n) hw
    change ((A n) w.1 + (RadialBallRetraction.extend R (remainder n) w).1,
      (B n) w.2 + (RadialBallRetraction.extend R (remainder n) w).2) = H n w
    rw [same]
    apply Prod.ext
    · change (A n) w.1 + ((H n w).1 - (A n) w.1) = (H n w).1
      abel
    · change (B n) w.2 + ((H n w).2 - (B n) w.2) = (H n w).2
      abel
  let sequence : ℤ →ᵇ U × S := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete z R bounded
  have sequence_step : ∀ n, d.map n (sequence (n + 1)) = sequence n := by
    intro n
    change d.map n (z (n + 1)) = z n
    rw [agreement n _ (bounded (n + 1))]
    exact step n
  have zero_step : ∀ n, d.map n ((0 : ℤ →ᵇ U × S) (n + 1)) = (0 : ℤ →ᵇ U × S) n := by
    intro n
    change d.map n 0 = 0
    rw [agreement n 0 (by simpa only [norm_zero] using positive.le)]
    exact origin n
  have same : sequence = 0 := (d.orbit_unique sequence sequence_step).trans
    (d.orbit_unique 0 zero_step).symm
  intro n
  exact congrArg (fun v : ℤ →ᵇ U × S => v n) same

end LeanShared.LocalHyperbolicOrbitUniqueness
