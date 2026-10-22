module

public import LeanShared.Dynamics.LocalHyperbolicShadowing
public import LeanShared.Dynamics.HyperbolicFiniteWindowDecay

/-! Actual local differentiable split maps give exponential finite-window
matching. Only the derivative estimates on the original ball are used;
the radial extension and its contraction are constructed in the proof. -/
public noncomputable section
namespace LeanShared.LocalHyperbolicShadowing
open Set
open scoped NNReal

set_option maxHeartbeats 1600000 in
theorem finite_window_distance
    {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    (H : ℤ → U × S → U × S) (A : ℤ → U ≃L[ℝ] U) (B : ℤ → S →L[ℝ] S)
    (k δ : ℝ≥0) (small : k + δ * 2 < 1)
    (inverse : ∀ m, ‖(A m).symm.toContinuousLinearMap‖ ≤ (k : ℝ))
    (stable : ∀ m, ‖B m‖ ≤ (k : ℝ))
    (R : ℝ) (positive : 0 < R)
    (differentiable : ∀ m v, ‖v‖ ≤ R → DifferentiableAt ℝ (H m) v)
    (derivative : ∀ m v, ‖v‖ ≤ R →
      ‖fderiv ℝ (H m) v - (A m).toContinuousLinearMap.prodMap (B m)‖ ≤ (δ : ℝ))
    (centered : ∀ m, H m 0 = 0)
    (z w : ℤ → U × S) (n : ℕ)
    (zbounded : ∀ j : ℕ, j ≤ n → ‖z j‖ ≤ R)
    (wbounded : ∀ j : ℕ, j ≤ n → ‖w j‖ ≤ R)
    (zstep : ∀ j : ℕ, j < n → H j (z (j + 1)) = z j)
    (wstep : ∀ j : ℕ, j < n → H j (w (j + 1)) = w j) :
    ∀ j : ℕ, j ≤ n → dist (z j) (w j) ≤
      ((k + δ * 2 : ℝ≥0) : ℝ) ^ min j (n - j) * (2 * R) := by
  let block := fun m => (A m).toContinuousLinearMap.prodMap (B m)
  let remainder := fun m v => H m v - block m v
  have remainder_diff (m : ℤ) (v : U × S) (hv : ‖v‖ ≤ R) :
      DifferentiableAt ℝ (remainder m) v :=
    (differentiable m v hv).sub (block m).differentiableAt
  have remainder_bound (m : ℤ) (v : U × S) (hv : ‖v‖ ≤ R) :
      ‖fderiv ℝ (remainder m) v‖ ≤ (δ : ℝ) := by
    have expression : remainder m = H m - ⇑(block m) := rfl
    rw [expression, fderiv_sub (differentiable m v hv) (block m).differentiableAt,
      (block m).fderiv]
    exact derivative m v hv
  let d : HyperbolicShadowing.Data U S := {
    expanding := A
    contracting := B
    nonlinear := fun m => RadialBallRetraction.extend R (remainder m)
    k := k
    δ := δ * 2
    small := small
    inverse_bound := fun m => ContinuousLinearMap.lipschitzWith_of_opNorm_le (inverse m)
    stable_bound := fun m => ContinuousLinearMap.lipschitzWith_of_opNorm_le (stable m)
    nonlinear_bound := fun m => RadialBallRetraction.lipschitz_extend_of_fderiv
      R positive (remainder m) δ
      (fun v hv => remainder_diff m v (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv))
      (fun v hv => remainder_bound m v (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv))
    error := 0
    nonlinear_zero := fun m => by
      rw [RadialBallRetraction.extend_eq R positive (remainder m)
        (by simpa only [norm_zero] using positive.le)]
      simp only [remainder, centered, map_zero, sub_zero, norm_zero, le_refl]
  }
  have agreement (m : ℤ) (v : U × S) (hv : ‖v‖ ≤ R) : d.map m v = H m v := by
    have same := RadialBallRetraction.extend_eq R positive (remainder m) hv
    change ((A m) v.1 + (RadialBallRetraction.extend R (remainder m) v).1,
      (B m) v.2 + (RadialBallRetraction.extend R (remainder m) v).2) = H m v
    rw [same]
    apply Prod.ext
    · change (A m) v.1 + ((H m v).1 - (A m) v.1) = (H m v).1
      abel
    · change (B m) v.2 + ((H m v).2 - (B m) v.2) = (H m v).2
      abel
  apply d.finite_window_steps z w (2 * R) n
  · intro j hj
    rw [agreement j _ (by simpa only [Nat.cast_add, Nat.cast_one] using zbounded (j + 1) (by omega))]
    exact zstep j hj
  · intro j hj
    rw [agreement j _ (by simpa only [Nat.cast_add, Nat.cast_one] using wbounded (j + 1) (by omega))]
    exact wstep j hj
  · intro j hj
    calc
      dist (z j) (w j) ≤ ‖z j‖ + ‖w j‖ := dist_le_norm_add_norm _ _
      _ ≤ R + R := add_le_add (zbounded j hj) (wbounded j hj)
      _ = 2 * R := by ring

end LeanShared.LocalHyperbolicShadowing
