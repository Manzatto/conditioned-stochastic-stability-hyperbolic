module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniAnnealed
public import LeanShared.Analysis.PerturbationModulus

/-! # The actual mixednorm limit constructs the precise KL perturbation modulus

Uniform finite-block estimates and actual mixednorm operator convergence suffice.
Monotonicity, upper semicontinuity and strict positivity of the primary-source
modulus are produced internally; no quantitative power law is required.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
open LeanShared.TwoNormNormalization

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem exists_hypotheses_of_actual_annealed_limit
    [CompleteSpace E] [CompleteSpace W]
    {Ω : Type*} [MeasurableSpace Ω] (noise : Measure Ω) [IsProbabilityMeasure noise]
    (A : ℝ≥0 → Ω → E →L[ℂ] E)
    (hmeas : ∀ ε x, AEStronglyMeasurable (fun ω => A ε ω x) noise)
    (i : E →L[ℂ] W) (hi : Function.Injective i) (hic : IsCompactOperator i)
    (window : ℝ≥0) (hwindow : 0 < window)
    (N : ℕ) (hN : 0 < N) (ρ C₀ M L B scale : ℝ)
    (hρ : 0 < ρ) (hρC₀ : ρ < C₀) (hM : 0 ≤ M) (hMC₀ : M ≤ C₀)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hscale : 1 ≤ scale) (hρscale : ρ < scale)
    (hA : ∀ ε ω, ‖A ε ω‖ ≤ L)
    (hweak : ∀ ε ≤ window, ∀ ω x, ‖i (A ε ω x)‖ ≤ M * ‖i x‖)
    (hblock : ∀ ε ≤ window, ∀ word : List Ω, word.length = N → ∀ x,
      ‖LeanShared.FiniteBlockAnnealedEstimates.listWord (A ε) word x‖ ≤
        ρ ^ N * ‖x‖ + B * ‖i x‖)
    :
    let P := fun ε => LeanShared.AnnealedOperatorBounds.pointwiseAnnealed noise (A ε) (hmeas ε) L (hA ε)
    (∀ ε ≤ window, NoResidualAbove (normalizedOperator (P ε) scale) (ρ / scale)) →
    Tendsto (fun ε => ‖i.comp (P ε - P 0)‖) (𝓝 0) (𝓝 0) →
    ∃ h : Hypotheses (fun ε => normalizedOperator (P ε) scale) (weakEmbedding i),
      h.alpha = ρ / scale ∧ h.weakRate = C₀ / scale ∧ IsCompactOperator (weakEmbedding i) := by
  dsimp only
  intro hres hlimit
  let P := fun ε => LeanShared.AnnealedOperatorBounds.pointwiseAnnealed noise (A ε) (hmeas ε) L (hA ε)
  obtain ⟨τ, v, hv, hτmono, hτusc, hτpos, hτzero, hτbound⟩ :=
    LeanShared.PerturbationModulus.exists_modulus_window
      (fun ε => ‖i.comp (P ε - P 0)‖) (fun _ => norm_nonneg _) hlimit
  exact exists_hypotheses_of_actual_annealed_family noise A hmeas i hi hic
    (min window v) (lt_min hwindow hv) N hN ρ C₀ M L B scale hρ hρC₀ hM hMC₀ hL hB
    hscale hρscale hA
    (fun ε hε => hweak ε (hε.trans (min_le_left _ _)))
    (fun ε hε => hblock ε (hε.trans (min_le_left _ _)))
    τ hτmono hτusc hτpos hτzero
    (fun ε hε => hres ε (hε.trans (min_le_left _ _)))
    (fun ε hε => hτbound ε (hε.trans (min_le_right _ _)))

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
