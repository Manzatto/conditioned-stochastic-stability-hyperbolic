module

public import LeanShared.Dynamics.HyperbolicBasicSet
public import LeanShared.Geometry.FractionalManifoldRegularity

/-! Ordinary nonmixing local analytic geometry. Every retained hyperbolic
basic set, including a periodic/nonmixing subordinate set, may carry this
datum. No mixing, leading eigenpair, compact embedding or noisy conclusion
is included. -/

@[expose] public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

/-- Regular local hyperbolic data with the actual tangent splitting. -/
structure BasicAnalyticData (T : M ≃ₜ M) (g : M → ℝ) (Λ V : Set M) where
  r : ℝ
  regularity_gt_one : 1 < r
  map_regular : FractionalManifoldRegularity.Regular (E := E) (F := E) r (T : M → M)
  inverse_regular : FractionalManifoldRegularity.Regular (E := E) (F := E) r (T.symm : M → M)
  basic : BasicData (E := E) T Λ V
  weight_regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (r - 1) g
  weight_nonnegative : ∀ x, 0 ≤ g x
  weight_supported : tsupport g ⊆ V
  weight_positive : ∀ x ∈ Λ, 0 < g x

namespace BasicAnalyticData
omit [FiniteDimensional ℝ E]
variable {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M}
  (h : BasicAnalyticData (E := E) T g Λ V)
include h
theorem compact_core : IsCompact Λ := h.basic.hyperbolic.compact
theorem nonempty_core : Λ.Nonempty := h.basic.nonempty
theorem actual_isolated_core : Λ = LeanShared.isolatedCore T (closure V) := h.basic.isolated
end BasicAnalyticData
end ConditionedStochasticStabilityHyperbolic.Paper
