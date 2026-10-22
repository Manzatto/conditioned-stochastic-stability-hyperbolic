module
public import LeanShared.Dynamics.RandomHyperbolicCocyclePlaques
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-! Actual manifold transport of the constructed nonautonomous random
plaques, using the coherent (time-dependent) chart at each reference point. -/
public noncomputable section
namespace LeanShared.RandomCocycleChartTransport
open Set Filter ControlledPlaqueClosure
open scoped Topology

structure Data (M Ω U S : Type*) [TopologicalSpace M] [TopologicalSpace Ω]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup S] [NormedSpace ℝ S] where
  coordinates : ℕ → OpenPartialHomeomorph M (U × S)
  localMap : RandomHyperbolicCocyclePlaques.Data Ω U S
  map : ℕ → M × Ω → M
  target : ∀ n, Metric.ball 0 localMap.radius ⊆ (coordinates n).target
  conjugacy : ∀ n ω z, ‖z‖ < localMap.radius →
    map n ((coordinates (n + 1)).symm z, ω) ∈ (coordinates n).source ∧
      coordinates n (map n ((coordinates (n + 1)).symm z, ω)) = localMap.map n ω z

namespace Data
variable {M Ω U S : Type*} [TopologicalSpace M] [TopologicalSpace Ω]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup S] [NormedSpace ℝ S]

@[expose] def collar (d : Data M Ω U S) (n : ℕ) : Set M :=
  {x | x ∈ (d.coordinates n).source ∧ ‖d.coordinates n x‖ < d.localMap.radius}

@[expose] def plaque [CompleteSpace U] [CompleteSpace S] (d : Data M Ω U S)
    (path : ℤ → Ω) : Set M := (d.coordinates 0).symm '' d.localMap.plaque path

private theorem target_of_norm (d : Data M Ω U S) (n : ℕ) {z : U × S}
    (inside : ‖z‖ < d.localMap.radius) : z ∈ (d.coordinates n).target :=
  d.target n (by simpa only [Metric.mem_ball, dist_zero_right] using inside)

theorem backward [CompleteSpace U] [CompleteSpace S] (d : Data M Ω U S)
    (path : ℤ → Ω) (x : M) (member : x ∈ d.plaque path) :
    ∃ b : ℕ → M, b 0 = x ∧ (∀ n, b n ∈ d.collar n) ∧
      ∀ n, d.map n (b (n + 1), backwardNoise path n) = b n := by
  obtain ⟨z,hz,image⟩ := member
  obtain ⟨b,initial,inside,step⟩ := d.localMap.backward path z hz
  refine ⟨fun n => (d.coordinates n).symm (b n), ?_, ?_, ?_⟩
  · change (d.coordinates 0).symm (b 0) = x
    rw [initial,image]
  · intro n
    have target := target_of_norm d n (inside n)
    exact ⟨(d.coordinates n).map_target target, by
      rw [(d.coordinates n).right_inv target]
      exact inside n⟩
  · intro n
    have relation := d.conjugacy n (backwardNoise path n) (b (n + 1)) (inside (n + 1))
    calc
      _ = (d.coordinates n).symm (d.coordinates n
          (d.map n ((d.coordinates (n + 1)).symm (b (n + 1)), backwardNoise path n))) :=
        ((d.coordinates n).left_inv relation.1).symm
      _ = (d.coordinates n).symm (b n) := by rw [relation.2,step n]

theorem local_backward [CompleteSpace U] [CompleteSpace S] (d : Data M Ω U S)
    (path : ℤ → Ω) (b : ℕ → M) (inside : ∀ n, b n ∈ d.collar n)
    (step : ∀ n, d.map n (b (n + 1), backwardNoise path n) = b n) : b 0 ∈ d.plaque path := by
  have localStep (n : ℕ) : d.localMap.map n (backwardNoise path n)
      (d.coordinates (n + 1) (b (n + 1))) = d.coordinates n (b n) := by
    have relation := d.conjugacy n (backwardNoise path n)
      (d.coordinates (n + 1) (b (n + 1))) (inside (n + 1)).2
    rw [(d.coordinates (n + 1)).left_inv (inside (n + 1)).1,step n] at relation
    exact relation.2.symm
  exact ⟨d.coordinates 0 (b 0), d.localMap.local_backward path
    (fun n => d.coordinates n (b n)) (fun n => (inside n).2) localStep,
    (d.coordinates 0).left_inv (inside 0).1⟩

theorem lower [CompleteSpace U] [CompleteSpace S] (d : Data M Ω U S)
    (path : ℤ → Ω) (paths : ℕ → ℤ → Ω) (converges : Tendsto paths atTop (𝓝 path))
    (x : M) (member : x ∈ d.plaque path) :
    ∃ xn : ℕ → M, Tendsto xn atTop (𝓝 x) ∧ ∀ n, xn n ∈ d.plaque (paths n) := by
  obtain ⟨z,hz,image⟩ := member
  obtain ⟨zn,limit,belongs⟩ := d.localMap.lower path paths converges z hz
  obtain ⟨b,initial,inside,_step⟩ := d.localMap.backward path z hz
  have coordinateInside : ‖z‖ < d.localMap.radius := by simpa only [initial] using inside 0
  have continuous := (d.coordinates 0).continuousAt_symm (target_of_norm d 0 coordinateInside)
  refine ⟨fun n => (d.coordinates 0).symm (zn n), ?_, fun n => ⟨zn n,belongs n,rfl⟩⟩
  simpa only [Function.comp_def,image] using continuous.tendsto.comp limit

end Data
end LeanShared.RandomCocycleChartTransport
