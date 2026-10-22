module
public import LeanShared.Dynamics.HyperbolicLocalPlaques
public import LeanShared.Analysis.LocalLipschitzRadialExtension
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Tactic.Abel

/-! A local unstable-graph construction directly from the derivative of the
actual nonlinear maps. The nonlinear remainder and its global extension are
constructed, not source fields. Only local derivatives relative to the
hyperbolic block linearization, its inverse/stable bounds, and an explicit
forcing margin are required. -/
public noncomputable section
namespace LeanShared.LocalHyperbolicGraph
open scoped NNReal BoundedContinuousFunction

structure Data (U S : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] where
  map : ℕ → U × S → U × S
  expanding : ℕ → U ≃L[ℝ] U
  contracting : ℕ → S →L[ℝ] S
  k : ℝ≥0
  δ : ℝ≥0
  small : k + δ * 2 < 1
  inverse_bound : ∀ n, ‖(expanding n).symm.toContinuousLinearMap‖ ≤ (k : ℝ)
  stable_bound : ∀ n, ‖contracting n‖ ≤ (k : ℝ)
  radius : ℝ
  radius_positive : 0 < radius
  differentiable : ∀ n z, ‖z‖ ≤ radius → DifferentiableAt ℝ (map n) z
  derivative_bound : ∀ n z, ‖z‖ ≤ radius →
    ‖fderiv ℝ (map n) z - (expanding n).toContinuousLinearMap.prodMap (contracting n)‖ ≤ (δ : ℝ)
  zero_bound : ℝ
  map_zero_bound : ∀ n, ‖map n 0‖ ≤ zero_bound
  forcing : ((k : ℝ) + 1) * zero_bound < (1 - (k + δ * 2 : ℝ≥0)) * radius

namespace Data
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

@[expose] def block (d : Data U S) (n : ℕ) : U × S →L[ℝ] U × S :=
  (d.expanding n).toContinuousLinearMap.prodMap (d.contracting n)

@[expose] def remainder (d : Data U S) (n : ℕ) (z : U × S) : U × S := d.map n z - d.block n z

theorem remainder_differentiable (d : Data U S) (n : ℕ) (z : U × S) (inside : ‖z‖ ≤ d.radius) :
    DifferentiableAt ℝ (d.remainder n) z :=
  (d.differentiable n z inside).sub (d.block n).differentiableAt

theorem remainder_derivative (d : Data U S) (n : ℕ) (z : U × S) (inside : ‖z‖ ≤ d.radius) :
    ‖fderiv ℝ (d.remainder n) z‖ ≤ (d.δ : ℝ) := by
  change ‖fderiv ℝ (fun x => d.map n x - d.block n x) z‖ ≤ (d.δ : ℝ)
  have function_eq : (fun x => d.map n x - d.block n x) = d.map n - ⇑(d.block n) := by
    funext x
    rfl
  rw [function_eq, fderiv_sub (d.differentiable n z inside) (d.block n).differentiableAt,
    (d.block n).fderiv]
  exact d.derivative_bound n z inside

@[expose] def extension (d : Data U S) : HyperbolicBackwardGraph.Data U S where
  expanding := d.expanding
  contracting := d.contracting
  nonlinear := fun n => RadialBallRetraction.extend d.radius (d.remainder n)
  k := d.k
  δ := d.δ * 2
  small := d.small
  inverse_bound := fun n => ContinuousLinearMap.lipschitzWith_of_opNorm_le (d.inverse_bound n)
  stable_bound := fun n => ContinuousLinearMap.lipschitzWith_of_opNorm_le (d.stable_bound n)
  nonlinear_bound := fun n => RadialBallRetraction.lipschitz_extend_of_fderiv
    d.radius d.radius_positive (d.remainder n) d.δ
    (fun z hz => d.remainder_differentiable n z (by simpa only
      [Metric.mem_closedBall, dist_zero_right] using hz))
    (fun z hz => d.remainder_derivative n z (by simpa only
      [Metric.mem_closedBall, dist_zero_right] using hz))
  zero_bound := d.zero_bound
  nonlinear_zero := fun n => by
    rw [RadialBallRetraction.extend_eq d.radius d.radius_positive (d.remainder n)
      (by simpa only [norm_zero] using d.radius_positive.le), remainder, map_zero, sub_zero]
    exact d.map_zero_bound n

theorem extension_forward (d : Data U S) (n : ℕ) (z : U × S) (inside : ‖z‖ ≤ d.radius) :
    d.extension.forward n z = d.map n z := by
  have agreement := RadialBallRetraction.extend_eq d.radius d.radius_positive (d.remainder n) inside
  change ((d.expanding n) z.1 + (RadialBallRetraction.extend d.radius (d.remainder n) z).1,
    (d.contracting n) z.2 + (RadialBallRetraction.extend d.radius (d.remainder n) z).2) = _
  rw [agreement]
  apply Prod.ext
  · change (d.expanding n) z.1 + ((d.map n z).1 - (d.expanding n) z.1) = (d.map n z).1
    abel
  · change (d.contracting n) z.2 + ((d.map n z).2 - (d.contracting n) z.2) = (d.map n z).2
    abel

@[expose] def plaque [CompleteSpace U] [CompleteSpace S] (d : Data U S) : Set (U × S) :=
  HyperbolicBackwardGraph.plaque d.extension d.radius

theorem backward [CompleteSpace U] [CompleteSpace S] (d : Data U S)
    (z : U × S) (member : z ∈ d.plaque) :
    ∃ b : ℕ → U × S, b 0 = z ∧ (∀ n, ‖b n‖ < d.radius) ∧
      ∀ n, d.map n (b (n + 1)) = b n := by
  obtain ⟨b, initial, inside, step⟩ :=
    HyperbolicBackwardGraph.plaque_backward d.extension d.radius d.forcing z member
  refine ⟨b, initial, inside, fun n => ?_⟩
  rw [← d.extension_forward n (b (n + 1)) (inside (n + 1)).le]
  exact step n

theorem local_backward [CompleteSpace U] [CompleteSpace S] (d : Data U S)
    (b : ℕ → U × S) (inside : ∀ n, ‖b n‖ < d.radius)
    (step : ∀ n, d.map n (b (n + 1)) = b n) : b 0 ∈ d.plaque := by
  apply HyperbolicBackwardGraph.plaque_local_backward d.extension d.radius b inside
  intro n
  rw [d.extension_forward n (b (n + 1)) (inside (n + 1)).le]
  exact step n

end Data
end LeanShared.LocalHyperbolicGraph
