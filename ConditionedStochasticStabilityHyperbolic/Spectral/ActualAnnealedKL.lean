module

public import ConditionedStochasticStabilityHyperbolic.Spectral.EssentialRadiusBridge

/-! The classical KL theorem applied to actual varying-law annealed bounds.
The hypotheses, perturbation modulus and residual/Fredholm condition are all
constructed from the finite block estimates and genuine mixed-norm limit. -/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
open LeanShared.TwoNormNormalization

variable {E W Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] [MeasurableSpace Ω]

structure ActualAnnealedInputs
    (noise : ℝ≥0 → Measure Ω) (hprob : ∀ ε, IsProbabilityMeasure (noise ε))
    (i : E →L[ℂ] W) (scale : ℝ) where
  generator : ℝ≥0 → Ω → E →L[ℂ] E
  measurable : ∀ ε x, AEStronglyMeasurable (fun ω => generator ε ω x) (noise ε)
  window : ℝ≥0
  window_pos : 0 < window
  blockLength : ℕ
  blockLength_pos : 0 < blockLength
  principal : ℝ
  weakRate : ℝ
  weakOneStep : ℝ
  operatorBound : ℝ
  remainder : ℝ
  principal_pos : 0 < principal
  principal_weak : principal < weakRate
  weakOneStep_nonneg : 0 ≤ weakOneStep
  weakOneStep_rate : weakOneStep ≤ weakRate
  operatorBound_nonneg : 0 ≤ operatorBound
  remainder_nonneg : 0 ≤ remainder
  scale_ge_one : 1 ≤ scale
  principal_scale : principal < scale
  generator_bound : ∀ ε ω, ‖generator ε ω‖ ≤ operatorBound
  weak_bound : ∀ ε ≤ window, ∀ ω x,
    ‖i (generator ε ω x)‖ ≤ weakOneStep * ‖i x‖
  block_bound : ∀ ε ≤ window, ∀ word : List Ω, word.length = blockLength → ∀ x,
    ‖LeanShared.FiniteBlockAnnealedEstimates.listWord (generator ε) word x‖ ≤
      principal ^ blockLength * ‖x‖ + remainder * ‖i x‖
  perturbation :
    let P := varyingNoiseOperator noise hprob generator measurable operatorBound generator_bound
    Tendsto (fun ε => ‖i.comp (P ε - P 0)‖) (𝓝 0) (𝓝 0)

def ActualAnnealedInputs.operator
    {noise : ℝ≥0 → Measure Ω} {hprob : ∀ ε, IsProbabilityMeasure (noise ε)}
    {i : E →L[ℂ] W} {scale : ℝ} (s : ActualAnnealedInputs noise hprob i scale) :
    ℝ≥0 → E →L[ℂ] E :=
  fun ε => normalizedOperator
    (varyingNoiseOperator noise hprob s.generator s.measurable s.operatorBound s.generator_bound ε) scale

/-- Both named classical analytic theorems are applied to their actual
hypotheses; no noisy spectral confinement or rank-one output is assumed. -/
theorem ActualAnnealedInputs.exists_projector_outputs
    {noise : ℝ≥0 → Measure Ω} {hprob : ∀ ε, IsProbabilityMeasure (noise ε)}
    {i : E →L[ℂ] W} {scale : ℝ} (s : ActualAnnealedInputs noise hprob i scale)
    (essential : EssentialRadiusContract (E := E) (W := W))
    (kl : ClassicalContract (E := E) (W := W))
    (hi : Function.Injective i) (hic : IsCompactOperator i)
    (d : DeterministicLeading (s.operator 0)) (q δ : ℝ)
    (hαq : s.principal / scale < q) (hqr : q < d.rate)
    (hqweak : q < s.weakRate / scale) (hsubq : d.subordinate < q)
    (hδ : 0 < δ) (hδsub : δ < q - d.subordinate) (hδlead : δ < d.rate - q) :
    Nonempty (ProjectorOutputs s.operator (weakEmbedding i) d q δ) := by
  obtain ⟨h, hα, hweak, _⟩ := exists_hypotheses_of_varying_noise_classical_radius
    essential noise hprob s.generator s.measurable i hi hic s.window s.window_pos
    s.blockLength s.blockLength_pos s.principal s.weakRate s.weakOneStep s.operatorBound s.remainder scale
    s.principal_pos s.principal_weak s.weakOneStep_nonneg s.weakOneStep_rate
    s.operatorBound_nonneg s.remainder_nonneg s.scale_ge_one s.principal_scale
    s.generator_bound s.weak_bound s.block_bound s.perturbation
  exact kl s.operator (weakEmbedding i) h d q δ (hα.symm ▸ hαq) hqr
    (hweak.symm ▸ hqweak) hsubq hδ hδsub hδlead

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
