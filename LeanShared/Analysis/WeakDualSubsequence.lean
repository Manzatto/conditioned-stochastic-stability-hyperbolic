module
public import Mathlib.Analysis.Normed.Module.WeakDual

/-! A uniformly bounded sequence of actual continuous linear functionals on a
separable predual has a subsequence converging on every predual vector. -/
public noncomputable section
open Filter Topology TopologicalSpace
namespace LeanShared.WeakDualSubsequence
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [SeparableSpace E]

theorem exists_pointwise (f : ℕ → E →L[𝕜] 𝕜) (B : ℝ) (bound : ∀ n, ‖f n‖ ≤ B) :
    ∃ g : E →L[𝕜] 𝕜, ‖g‖ ≤ B ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ x : E, Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x)) := by
  have members (n : ℕ) : StrongDual.toWeakDual (f n) ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) B := by
    change dist (f n) 0 ≤ B
    simpa only [dist_zero_right] using bound n
  obtain ⟨g,hg,φ,mono,converges⟩ :=
    (WeakDual.isSeqCompact_closedBall 𝕜 E (0 : StrongDual 𝕜 E) B) members
  refine ⟨WeakDual.toStrongDual g,?_,φ,mono,fun x => ?_⟩
  · simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right] using hg
  · have evaluation := ((WeakDual.eval_continuous x).tendsto g).comp converges
    exact evaluation
end LeanShared.WeakDualSubsequence
