module

public import LeanShared.Dynamics.FiniteBoundaryHyperbolicTube
public import LeanShared.Analysis.LocalLipschitzRadialExtension
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Tactic.Abel

/-! Construct finite two-boundary shooting from local differentiable chart
maps. The nonlinear extension and its global contraction bounds are proved
from actual local derivatives; the original maps are preserved in the ball. -/
public noncomputable section
namespace LeanShared.LocalFiniteBoundaryShootingBlocks
open scoped NNReal

set_option maxHeartbeats 1600000 in
theorem construct
    {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] (N : ℕ)
    (H : Fin N → U × S → U × S) (A : Fin N → U ≃L[ℝ] U)
    (B : Fin N → S →L[ℝ] S) (k δ : ℝ≥0) (small : k + δ * 2 < 1)
    (inverse : ∀ i, ‖(A i).symm.toContinuousLinearMap‖ ≤ (k : ℝ))
    (stable : ∀ i, ‖B i‖ ≤ (k : ℝ)) (R : ℝ) (positive : 0 < R)
    (differentiable : ∀ i z, ‖z‖ ≤ R → DifferentiableAt ℝ (H i) z)
    (derivative : ∀ i z, ‖z‖ ≤ R →
      ‖fderiv ℝ (H i) z - (A i).toContinuousLinearMap.prodMap (B i)‖ ≤ (δ : ℝ))
    (origin : ∀ i, H i 0 = 0) :
    ∃ d : FiniteBoundaryHyperbolicTransform.Data U S N,
      d.expanding = A ∧ d.contracting = B ∧
      d.k = k ∧ d.δ = δ * 2 ∧ ∀ i z, ‖z‖ ≤ R → d.map i z = H i z := by
  let block := fun i => (A i).toContinuousLinearMap.prodMap (B i)
  let remainder := fun i z => H i z - block i z
  have remainder_diff (i : Fin N) (z : U × S) (hz : ‖z‖ ≤ R) :
      DifferentiableAt ℝ (remainder i) z :=
    (differentiable i z hz).sub (block i).differentiableAt
  have remainder_bound (i : Fin N) (z : U × S) (hz : ‖z‖ ≤ R) :
      ‖fderiv ℝ (remainder i) z‖ ≤ (δ : ℝ) := by
    have expression : remainder i = H i - ⇑(block i) := by funext v; rfl
    rw [expression, fderiv_sub (differentiable i z hz) (block i).differentiableAt,
      (block i).fderiv]
    exact derivative i z hz
  let d : FiniteBoundaryHyperbolicTransform.Data U S N := {
    expanding := A
    contracting := B
    nonlinear := fun i => RadialBallRetraction.extend R (remainder i)
    k := k
    δ := δ * 2
    small := small
    inverse_bound := fun i => ContinuousLinearMap.lipschitzWith_of_opNorm_le (inverse i)
    stable_bound := fun i => ContinuousLinearMap.lipschitzWith_of_opNorm_le (stable i)
    nonlinear_bound := fun i => RadialBallRetraction.lipschitz_extend_of_fderiv
      R positive (remainder i) δ
      (fun z hz => remainder_diff i z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz))
      (fun z hz => remainder_bound i z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz))
    nonlinear_zero := fun i => by
      rw [RadialBallRetraction.extend_eq R positive (remainder i)
        (by simpa only [norm_zero] using positive.le)]
      simp only [remainder, origin, map_zero, sub_self]
  }
  refine ⟨d, rfl, rfl, rfl, rfl, fun i z hz => ?_⟩
  have same := RadialBallRetraction.extend_eq R positive (remainder i) hz
  change ((A i) z.1 + (RadialBallRetraction.extend R (remainder i) z).1,
    (B i) z.2 + (RadialBallRetraction.extend R (remainder i) z).2) = H i z
  rw [same]
  apply Prod.ext
  · change (A i) z.1 + ((H i z).1 - (A i) z.1) = (H i z).1
    abel
  · change (B i) z.2 + ((H i z).2 - (B i) z.2) = (H i z).2
    abel

end LeanShared.LocalFiniteBoundaryShootingBlocks
