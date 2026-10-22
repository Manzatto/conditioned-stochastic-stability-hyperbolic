module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniActualPerturbation
import Mathlib.Tactic.Linarith

/-! # Uniform annealed KL hypotheses with varying noise laws

The manuscript allows a bounded absolutely continuous full-support density
at every noise scale, without fixing that density as the scale varies. After
identifying the parameter cubes with one type, the probability law may still
vary. Uniform word bounds apply to each independent-word law separately and
require no convergence of those laws or a common operator-norm measurability
assumption.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal BigOperators
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
open LeanShared.TwoNormNormalization

variable {E W Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] [MeasurableSpace Ω]

/-- Actual evaluated Bochner averages with scale-dependent probability laws. -/
def varyingNoiseOperator
    (noise : ℝ≥0 → Measure Ω) (hprob : ∀ ε, IsProbabilityMeasure (noise ε))
    (A : ℝ≥0 → Ω → E →L[ℂ] E)
    (hmeas : ∀ ε x, AEStronglyMeasurable (fun ω => A ε ω x) (noise ε))
    (L : ℝ) (hA : ∀ ε ω, ‖A ε ω‖ ≤ L) (ε : ℝ≥0) : E →L[ℂ] E := by
  let _ := hprob ε
  exact LeanShared.AnnealedOperatorBounds.pointwiseAnnealed (noise ε) (A ε) (hmeas ε) L (hA ε)

/-- The actual varying-noise family produces KL hypotheses from uniform
finite-block bounds and genuine mixednorm convergence. Probability law
convergence and a fixed density are unnecessary. -/
theorem exists_hypotheses_of_varying_noise_limit
    (noise : ℝ≥0 → Measure Ω) (hprob : ∀ ε, IsProbabilityMeasure (noise ε))
    (A : ℝ≥0 → Ω → E →L[ℂ] E)
    (hmeas : ∀ ε x, AEStronglyMeasurable (fun ω => A ε ω x) (noise ε))
    (i : E →L[ℂ] W) (hi : Function.Injective i) (hic : IsCompactOperator i)
    (window : ℝ≥0) (hwindow : 0 < window)
    (N : ℕ) (hN : 0 < N) (ρ C₀ M L B scale : ℝ)
    (hρ : 0 < ρ) (hρC₀ : ρ < C₀) (hM : 0 ≤ M) (hMC₀ : M ≤ C₀)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hscale : 1 ≤ scale) (hρscale : ρ < scale)
    (hA : ∀ ε ω, ‖A ε ω‖ ≤ L)
    (hweak : ∀ ε ≤ window, ∀ ω x, ‖i (A ε ω x)‖ ≤ M * ‖i x‖)
    (hblock : ∀ ε ≤ window, ∀ word : List Ω, word.length = N → ∀ x,
      ‖LeanShared.FiniteBlockAnnealedEstimates.listWord (A ε) word x‖ ≤
        ρ ^ N * ‖x‖ + B * ‖i x‖) :
    let P := varyingNoiseOperator noise hprob A hmeas L hA
    (∀ ε ≤ window, NoResidualAbove (normalizedOperator (P ε) scale) (ρ / scale)) →
    Tendsto (fun ε => ‖i.comp (P ε - P 0)‖) (𝓝 0) (𝓝 0) →
    ∃ h : Hypotheses (fun ε => normalizedOperator (P ε) scale) (weakEmbedding i),
      h.alpha = ρ / scale ∧ h.weakRate = C₀ / scale ∧ IsCompactOperator (weakEmbedding i) := by
  dsimp only
  intro hres hlimit
  let P := varyingNoiseOperator noise hprob A hmeas L hA
  let Cs := ∑ r ∈ Finset.range N, (L / ρ) ^ r
  let Cw := B / (C₀ ^ N - ρ ^ N)
  have hCs : 0 ≤ Cs := Finset.sum_nonneg (fun _ _ => pow_nonneg (div_nonneg hL hρ.le) _)
  have hden : 0 < C₀ ^ N - ρ ^ N :=
    sub_pos.mpr (pow_lt_pow_left₀ hρC₀ hρ.le hN.ne')
  have hCw : 0 ≤ Cw := div_nonneg hB hden.le
  have hstrong : ∀ ε ≤ window, ∀ n x,
      ‖(P ε ^ n) x‖ ≤ Cs * ρ ^ n * ‖x‖ + Cw * C₀ ^ n * ‖i x‖ := by
    intro ε hε
    let _ := hprob ε
    exact (LeanShared.FiniteBlockAnnealedEstimates.annealed_twoNorm_bound (noise ε) (A ε)
      (hmeas ε) i N hN ρ C₀ M L B hρ hρC₀ hM hMC₀ hL hB (hA ε)
      (hweak ε hε) (hblock ε hε)).2.2
  have hweakP : ∀ ε ≤ window, ∀ n x, ‖i ((P ε ^ n) x)‖ ≤ 1 * C₀ ^ n * ‖i x‖ := by
    intro ε hε n x
    let _ := hprob ε
    have h := LeanShared.FiniteBlockAnnealedEstimates.annealed_weak_power_bound (noise ε) (A ε)
      (hmeas ε) L (hA ε) i M hM (hweak ε hε) n x
    exact h.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM hMC₀ n) (norm_nonneg (i x)))
  obtain ⟨τ, v, hv, hτmono, hτusc, hτpos, hτzero, hτbound⟩ :=
    LeanShared.PerturbationModulus.exists_modulus_window
      (fun ε => ‖i.comp (P ε - P 0)‖) (fun _ => norm_nonneg _) hlimit
  let h := hypothesesOfRaw P i hi (min window v) (lt_min hwindow hv) scale ρ C₀ 1 Cs Cw
    hscale hρ hρscale hρC₀ zero_lt_one hCs hCw
    (fun ε hε => hweakP ε (hε.trans (min_le_left _ _)))
    (fun ε hε => hstrong ε (hε.trans (min_le_left _ _)))
    (fun ε hε => hres ε (hε.trans (min_le_left _ _)))
    τ hτmono hτusc hτpos hτzero
    (fun ε hε => hτbound ε (hε.trans (min_le_right _ _)))
  exact ⟨h, rfl, rfl, normalized_weak_inclusion_compact i hic⟩

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
