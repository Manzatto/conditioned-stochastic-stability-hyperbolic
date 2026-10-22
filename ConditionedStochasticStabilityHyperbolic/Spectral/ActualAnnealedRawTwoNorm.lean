module
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedKL
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedZero
public import ConditionedStochasticStabilityHyperbolic.Spectral.CommonAmbientRawBounds

/-! The raw compact two-norm estimate of the zero-noise generator. The normalized KL hypotheses
built from the actual block bounds have strong rate `principal / scale`; multiplying back by the
scale gives the powers of the deterministic generator with strong rate `principal` against the
compact normalized weak embedding. -/
public noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
open LeanShared.TwoNormNormalization

variable {E W Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] [MeasurableSpace Ω]

theorem ActualAnnealedInputs.raw_two_norm
    {noise : ℝ≥0 → Measure Ω} {hprob : ∀ ε, IsProbabilityMeasure (noise ε)}
    {i : E →L[ℂ] W} {scale : ℝ} (s : ActualAnnealedInputs noise hprob i scale)
    (essential : EssentialRadiusContract (E := E) (W := W))
    (hi : Function.Injective i) (hic : IsCompactOperator i)
    (P : E →L[ℂ] E) (hzero : ∀ z, s.generator 0 z = P) :
    ∃ C D R : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ R ∧ IsCompactOperator (weakEmbedding i) ∧
      ∀ n x, ‖(P ^ n) x‖ ≤ C * s.principal ^ n * ‖x‖ + D * R ^ n * ‖weakEmbedding i x‖ := by
  obtain ⟨h, hα, _, hcomp⟩ := exists_hypotheses_of_varying_noise_classical_radius
    essential noise hprob s.generator s.measurable i hi hic s.window s.window_pos
    s.blockLength s.blockLength_pos s.principal s.weakRate s.weakOneStep s.operatorBound s.remainder
    scale s.principal_pos s.principal_weak s.weakOneStep_nonneg s.weakOneStep_rate
    s.operatorBound_nonneg s.remainder_nonneg s.scale_ge_one s.principal_scale
    s.generator_bound s.weak_bound s.block_bound s.perturbation
  have scalePos : 0 < scale := zero_lt_one.trans_le s.scale_ge_one
  have raw := CommonAmbientRawBounds.twoNorm_growth h 0 (zero_le) scale scalePos
  have identity : ((scale : ℂ) • s.operator 0) = P :=
    s.raw_zero_of_constant_generators scalePos.ne' P hzero
  have rate : scale * h.alpha = s.principal := by
    rw [hα]
    field_simp
  refine ⟨h.strongConstant, h.errorConstant, scale * h.weakRate, h.strongConstant_pos.le,
    h.errorConstant_pos.le, mul_nonneg scalePos.le (h.alpha_pos.trans h.alpha_lt_weakRate).le,
    hcomp, fun n x => ?_⟩
  have bound := raw n x
  rw [rate] at bound
  change ‖((((scale : ℂ) • s.operator 0) ^ n : E →L[ℂ] E)) x‖ ≤ _ at bound
  rw [identity] at bound
  exact bound

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
