module
public import ConditionedStochasticStabilityHyperbolic.Paper.BasicAnalyticData
public import LeanShared.Dynamics.HyperbolicExpansivity

/-! Literal fractional regularity and the actual compact hyperbolic splitting
imply two-sided metric expansivity. The continuous Riemannian metric is stated
explicitly: fiberwise inner products alone do not assert its base continuity. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.BasicAnalyticData
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

set_option maxHeartbeats 2400000 in
theorem exists_expansivity_radius
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M}
    (h : BasicAnalyticData (E := E) T g Λ V) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Λ, ∀ y ∈ Λ,
      (∀ j : ℕ, dist ((T : M → M)^[j] x) ((T : M → M)^[j] y) ≤ c ∧
        dist ((T.symm : M → M)^[j] x) ((T.symm : M → M)^[j] y) ≤ c) → x = y := by
  have hn : (1 : ℕ) ≤ ⌊h.r⌋₊ :=
    Nat.le_floor (by simpa only [Nat.cast_one] using h.regularity_gt_one.le)
  exact h.basic.exists_expansivity_radius
    (h.map_regular.differentiable.of_le (by exact_mod_cast hn))
    (h.inverse_regular.differentiable.of_le (by exact_mod_cast hn))

end ConditionedStochasticStabilityHyperbolic.Paper.BasicAnalyticData
