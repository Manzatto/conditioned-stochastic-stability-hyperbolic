module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedKL

/-! An actual weak completion may be replaced by a proved isometric model.
The complete block, growth and perturbation estimates are transported; none
is asserted as a new analytic source. -/

public noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {S W V Ω : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] [MeasurableSpace Ω]

omit [CompleteSpace S] [CompleteSpace W] [CompleteSpace V] in
theorem norm_isometry_comp (e : W ≃ₗᵢ[ℂ] V) (P : S →L[ℂ] W) :
    ‖e.toLinearIsometry.toContinuousLinearMap.comp P‖ = ‖P‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg P)
    intro x
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map] using P.le_opNorm x
  · apply P.opNorm_le_bound (norm_nonneg _)
    intro x
    have h := (e.toLinearIsometry.toContinuousLinearMap.comp P).le_opNorm x
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map] using h

@[expose] def ActualAnnealedInputs.transportWeak
    {law : ℝ≥0 → Measure Ω} {hprob : ∀ ε, IsProbabilityMeasure (law ε)}
    {i : S →L[ℂ] W} {scale : ℝ}
    (s : ActualAnnealedInputs law hprob i scale) (e : W ≃ₗᵢ[ℂ] V) :
    ActualAnnealedInputs law hprob (e.toLinearIsometry.toContinuousLinearMap.comp i) scale :=
  { s with
    weak_bound := by
      intro ε hε z x
      simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map]
        using s.weak_bound ε hε z x
    block_bound := by
      intro ε hε word hword x
      simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map]
        using s.block_bound ε hε word hword x
    perturbation := by
      simpa only [ContinuousLinearMap.comp_assoc, norm_isometry_comp] using s.perturbation }

omit [CompleteSpace S] [CompleteSpace W] [CompleteSpace V] in
@[simp] theorem ActualAnnealedInputs.transportWeak_generator
    {law : ℝ≥0 → Measure Ω} {hprob : ∀ ε, IsProbabilityMeasure (law ε)}
    {i : S →L[ℂ] W} {scale : ℝ}
    (s : ActualAnnealedInputs law hprob i scale) (e : W ≃ₗᵢ[ℂ] V) :
    (s.transportWeak e).generator = s.generator := rfl

omit [CompleteSpace S] [CompleteSpace W] [CompleteSpace V] in
@[simp] theorem ActualAnnealedInputs.transportWeak_operator
    {law : ℝ≥0 → Measure Ω} {hprob : ∀ ε, IsProbabilityMeasure (law ε)}
    {i : S →L[ℂ] W} {scale : ℝ}
    (s : ActualAnnealedInputs law hprob i scale) (e : W ≃ₗᵢ[ℂ] V) :
    (s.transportWeak e).operator = s.operator := rfl

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
