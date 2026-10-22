module

public import ConditionedStochasticStabilityHyperbolic.Paper.Hypotheses
public import Mathlib.Topology.Order.Compact

/-! The literal HL regularity gives continuous bounded weights. A single
scale can dominate the cutoff and original live weight and all analytic
rates, so operator normalization and process rescaling use the same scale. -/

@[expose] public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HL
open LeanShared
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M} (h : HL (E := E) T g Λ V)

include h

omit [FiniteDimensional ℝ E] in
theorem weight_continuous : Continuous g := h.weight_regular.differentiable.continuous

omit [FiniteDimensional ℝ E] in
theorem exists_shared_scale [CompactSpace M] {K : Set M} [CompactSpace K]
    (w : K → ℝ) (hw : Continuous w) (principal weak leading : ℝ) :
    ∃ R : ℝ, 1 ≤ R ∧ (∀ x, g x ≤ R) ∧ (∀ x, w x ≤ R) ∧
      principal < R ∧ weak < R ∧ leading < R := by
  obtain ⟨Cg, hg⟩ := isCompact_univ.exists_bound_of_continuousOn h.weight_continuous.continuousOn
  obtain ⟨Cw, hwbound⟩ := isCompact_univ.exists_bound_of_continuousOn hw.continuousOn
  let R := 1 + |Cg| + |Cw| + |principal| + |weak| + |leading|
  have hCg := abs_nonneg Cg
  have hCw := abs_nonneg Cw
  have hp := abs_nonneg principal
  have hweak := abs_nonneg weak
  have hlead := abs_nonneg leading
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [R]; linarith
  · intro x
    have hx := hg x (mem_univ x)
    have hnorm := le_abs_self (g x)
    have hC := le_abs_self Cg
    change g x ≤ 1 + |Cg| + |Cw| + |principal| + |weak| + |leading|
    rw [Real.norm_eq_abs] at hx
    linarith
  · intro x
    have hx := hwbound x (mem_univ x)
    have hnorm := le_abs_self (w x)
    have hC := le_abs_self Cw
    change w x ≤ 1 + |Cg| + |Cw| + |principal| + |weak| + |leading|
    rw [Real.norm_eq_abs] at hx
    linarith
  · have h := le_abs_self principal
    dsimp [R]; linarith
  · have h := le_abs_self weak
    dsimp [R]; linarith
  · have h := le_abs_self leading
    dsimp [R]; linarith

end ConditionedStochasticStabilityHyperbolic.Paper.HL
