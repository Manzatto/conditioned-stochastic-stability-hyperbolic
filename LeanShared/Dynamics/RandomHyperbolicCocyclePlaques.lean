module
public import LeanShared.Dynamics.LocalHyperbolicGraphContinuity
public import LeanShared.Dynamics.ControlledPlaqueClosure

/-! Random local unstable plaques for nonautonomous hyperbolic chart cocycles.
The expanding and stable blocks may vary along the entire reference orbit.
Only actual maps, their local derivatives and ordinary coefficient continuity
are inputs; lower semicontinuity/backward orbit/capture are derived. -/
public noncomputable section
namespace LeanShared.RandomHyperbolicCocyclePlaques
open Set Filter ControlledPlaqueClosure
open scoped Topology NNReal

structure Data (Ω U S : Type*) [TopologicalSpace Ω]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup S] [NormedSpace ℝ S] where
  map : ℕ → Ω → U × S → U × S
  expanding : ℕ → U ≃L[ℝ] U
  contracting : ℕ → S →L[ℝ] S
  k : ℝ≥0
  δ : ℝ≥0
  small : k + δ * 2 < 1
  inverse_bound : ∀ n, ‖(expanding n).symm.toContinuousLinearMap‖ ≤ (k : ℝ)
  stable_bound : ∀ n, ‖contracting n‖ ≤ (k : ℝ)
  radius : ℝ
  radius_positive : 0 < radius
  differentiable : ∀ n ω z, ‖z‖ ≤ radius → DifferentiableAt ℝ (map n ω) z
  derivative_bound : ∀ n ω z, ‖z‖ ≤ radius →
    ‖fderiv ℝ (map n ω) z - (expanding n).toContinuousLinearMap.prodMap (contracting n)‖ ≤ (δ : ℝ)
  zero_bound : ℝ
  map_zero_bound : ∀ n ω, ‖map n ω 0‖ ≤ zero_bound
  forcing : ((k : ℝ) + 1) * zero_bound < (1 - (k + δ * 2 : ℝ≥0)) * radius
  continuous : ∀ n, ContinuousOn (fun z : Ω × (U × S) => map n z.1 z.2)
    (univ ×ˢ Metric.closedBall 0 radius)

namespace Data
variable {Ω U S : Type*} [TopologicalSpace Ω]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup S] [NormedSpace ℝ S]

@[expose] def system (d : Data Ω U S) (path : ℤ → Ω) : LocalHyperbolicGraph.Data U S where
  map := fun n => d.map n (backwardNoise path n)
  expanding := d.expanding
  contracting := d.contracting
  k := d.k
  δ := d.δ
  small := d.small
  inverse_bound := fun n => d.inverse_bound n
  stable_bound := fun n => d.stable_bound n
  radius := d.radius
  radius_positive := d.radius_positive
  differentiable := fun n => d.differentiable n (backwardNoise path n)
  derivative_bound := fun n => d.derivative_bound n (backwardNoise path n)
  zero_bound := d.zero_bound
  map_zero_bound := fun n => d.map_zero_bound n (backwardNoise path n)
  forcing := d.forcing

@[expose] def plaque [CompleteSpace U] [CompleteSpace S] (d : Data Ω U S)
    (path : ℤ → Ω) : Set (U × S) := (d.system path).plaque

theorem backward [CompleteSpace U] [CompleteSpace S] (d : Data Ω U S)
    (path : ℤ → Ω) (z : U × S) (member : z ∈ d.plaque path) :
    ∃ b : ℕ → U × S, b 0 = z ∧ (∀ n, ‖b n‖ < d.radius) ∧
      ∀ n, d.map n (backwardNoise path n) (b (n + 1)) = b n :=
  (d.system path).backward z member

theorem local_backward [CompleteSpace U] [CompleteSpace S] (d : Data Ω U S)
    (path : ℤ → Ω) (b : ℕ → U × S) (inside : ∀ n, ‖b n‖ < d.radius)
    (step : ∀ n, d.map n (backwardNoise path n) (b (n + 1)) = b n) : b 0 ∈ d.plaque path :=
  (d.system path).local_backward b inside step

theorem lower [CompleteSpace U] [CompleteSpace S] (d : Data Ω U S)
    (path : ℤ → Ω) (paths : ℕ → ℤ → Ω) (converges : Tendsto paths atTop (𝓝 path))
    (z : U × S) (member : z ∈ d.plaque path) :
    ∃ zn : ℕ → U × S, Tendsto zn atTop (𝓝 z) ∧ ∀ n, zn n ∈ d.plaque (paths n) := by
  apply LocalHyperbolicGraph.plaque_lower d.system d.radius d.radius_positive (fun _ => rfl)
    (d.k + d.δ * 2) d.small (fun _ => le_rfl) d.zero_bound (fun _ => le_rfl)
    (fun n => (d.expanding n).continuous.comp continuous_snd)
    (fun n => (d.expanding n).symm.continuous.comp continuous_snd)
    (fun n => (d.contracting n).continuous.comp continuous_snd) _ path paths converges z member
  intro n
  have eval : Continuous (fun z : (ℤ → Ω) × (U × S) => (backwardNoise z.1 n, z.2)) :=
    ((continuous_apply (-(n : ℤ) - 1)).comp continuous_fst).prodMk continuous_snd
  exact (d.continuous n).comp eval.continuousOn (fun z hz => ⟨mem_univ _, hz.2⟩)

end Data
end LeanShared.RandomHyperbolicCocyclePlaques
