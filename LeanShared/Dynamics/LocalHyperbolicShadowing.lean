module
public import LeanShared.Dynamics.HyperbolicShadowing
public import LeanShared.Analysis.LocalLipschitzRadialExtension
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Tactic.Abel

/-! Local C1 hyperbolic maps with small forcing have a unique bounded entire
orbit. Its explicit error bound and nonlinear global extension are constructed
from actual local differential estimates. -/
public noncomputable section
namespace LeanShared.LocalHyperbolicShadowing
open Set
open scoped NNReal BoundedContinuousFunction

set_option maxHeartbeats 1600000 in
theorem exists_orbit
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
    (error : ℝ) (origin : ∀ n, ‖H n 0‖ ≤ error)
    (forcing : ((k:ℝ)+1)*error ≤ (1-(k+δ*2:ℝ≥0))*R) :
    ∃ z : ℤ →ᵇ U × S,
      ‖z‖ ≤ (((k:ℝ)+1)*error)/(1-(k+δ*2:ℝ≥0)) ∧
      (∀ n, H n (z (n+1)) = z n) ∧
      ∀ w : ℤ → U × S, (∀ n, ‖w n‖ ≤ R) →
        (∀ n, H n (w (n+1)) = w n) → ∀ n, w n = z n := by
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
    error := error
    nonlinear_zero := fun n => by
      rw [RadialBallRetraction.extend_eq R positive (remainder n) (by simpa only [norm_zero] using positive.le)]
      simpa only [remainder, map_zero, sub_zero] using origin n
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
  have normBound := d.shadowing_bound
  have radiusBound : ‖d.orbit‖ ≤ R := normBound.trans
    ((div_le_iff₀ d.transform_contracting.one_sub_K_pos).mpr (by simpa only [mul_comm] using forcing))
  have bounded (n:ℤ) : ‖d.orbit n‖ ≤ R := (d.orbit.norm_coe_le_norm n).trans radiusBound
  refine ⟨d.orbit,normBound,fun n=>?_,fun w hw hstep n=>?_⟩
  · rw [←agreement n _ (bounded (n+1))]
    exact d.orbit_step n
  · let sequence : ℤ →ᵇ U × S := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete w R hw
    have steps : ∀ j, d.map j (sequence (j+1))=sequence j := by
      intro j
      change d.map j (w (j+1))=w j
      rw [agreement j _ (hw (j+1))]
      exact hstep j
    exact congrArg (fun v:ℤ →ᵇ U×S=>v n) (d.orbit_unique sequence steps)

end LeanShared.LocalHyperbolicShadowing
