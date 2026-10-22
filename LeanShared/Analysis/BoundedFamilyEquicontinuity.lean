module
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity

/-! Relative sequential norm compactness of bounded continuous functions
implies equicontinuity. Limits may lie outside the given family. -/
public section
open Filter Topology
open scoped BoundedContinuousFunction
namespace LeanShared.BoundedFamilyEquicontinuity
variable {X I : Type*} [PseudoMetricSpace X]

theorem of_subsequences (F : I → X →ᵇ ℂ)
    (subsequences : ∀ u : ℕ → I, ∃ g : X →ᵇ ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => F (u (φ n))) atTop (𝓝 g)) :
    Equicontinuous (fun i x => F i x) := by
  classical
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  by_contra failure
  push Not at failure
  obtain ⟨ε,positive,bad⟩ := failure
  have badSeq (n : ℕ) : ∃ x : X, ∃ i : I,
      dist x x₀ < 1/((n:ℝ)+1) ∧ ε ≤ dist (F i x₀) (F i x) := by
    obtain ⟨x,near,i,far⟩ := bad (1/((n:ℝ)+1)) (by positivity)
    exact ⟨x,i,near,far⟩
  choose x u near far using badSeq
  have xconv : Tendsto x atTop (𝓝 x₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (near n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨g,φ,mono,conv⟩ := subsequences u
  have fixed := ((BoundedContinuousFunction.lipschitz_eval_const x₀).continuous.tendsto g).comp conv
  have moving := (continuous_eval.tendsto (g,x₀)).comp
    (conv.prodMk_nhds (xconv.comp mono.tendsto_atTop))
  have zero : Tendsto (fun n => dist (F (u (φ n)) x₀) (F (u (φ n)) (x (φ n))))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def,dist_self] using fixed.dist moving
  obtain ⟨n,hn⟩ := (zero.eventually (gt_mem_nhds positive)).exists
  exact (not_lt_of_ge (far (φ n))) hn
end LeanShared.BoundedFamilyEquicontinuity
