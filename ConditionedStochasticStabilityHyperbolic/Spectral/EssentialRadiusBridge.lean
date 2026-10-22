module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniVaryingNoise
import Mathlib.Tactic.Linarith

/-! # Deferred classical essential-radius criterion, applied to actual bounds

Hennion, *Quasi-compacité. Cas des noyaux lipschitziens et des noyaux
markoviens* (1995), Theorem 3.1 and the Nussbaum formula in Theorem 5.1:
https://www.numdam.org/item/PSMIR_1995___2_A6_0.pdf

The contract is the essential-radius/Fredholm corollary: relative compactness
of the weak inclusion and all-power two-norm bounds give essential radius at
most the strong rate. Outside that disk the spectral shift is Fredholm of
index zero, so injectivity implies surjectivity. It does not require the
image of the strong closed unit ball itself to be closed. The contraction
rate need not exceed the spectral radius: the essential-radius formulation,
rather than the quasi-compactness conclusion alone, is used here.

This classical operator theorem is a named input, not a global axiom. The
family-specific no-residual hypothesis is then proved from actual estimates.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal BigOperators
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
open LeanShared.TwoNormNormalization

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Classical essential-radius bound together with the index-zero Fredholm
alternative outside the essential spectral disk. No perturbation conclusion
or stochastic statement is contained in this input. -/
def EssentialRadiusContract : Prop :=
  ∀ (P : E →L[ℂ] E) (i : E →L[ℂ] W), Function.Injective i →
    IsCompactOperator i → ∀ (α R C D K : ℝ),
    0 < α → α < R → 0 ≤ C → 0 ≤ D → 0 ≤ K →
    (∀ n x, ‖i ((P ^ n) x)‖ ≤ K * R ^ n * ‖i x‖) →
    (∀ n x, ‖(P ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖) →
    ∀ z : ℂ, α < ‖z‖ → Function.Injective (z • (1 : E →L[ℂ] E) - P) →
      Function.Surjective (z • (1 : E →L[ℂ] E) - P)

theorem noResidual_of_compact_twoNorm
    (source : EssentialRadiusContract (E := E) (W := W))
    (P : E →L[ℂ] E) (i : E →L[ℂ] W) (hi : Function.Injective i)
    (hic : IsCompactOperator i) (α R C D K : ℝ)
    (hα : 0 < α) (hR : α < R) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hweak : ∀ n x, ‖i ((P ^ n) x)‖ ≤ K * R ^ n * ‖i x‖)
    (hstrong : ∀ n x, ‖(P ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖) :
    NoResidualAbove P α := by
  intro z hz hinj
  exact (source P i hi hic α R C D K hα hR hC hD hK hweak hstrong z hz hinj).denseRange

/-- Both actual scalar normalizations preserve the hypotheses of the
classical essential-radius criterion. -/
theorem noResidual_of_normalized_raw_bounds
    (source : EssentialRadiusContract (E := E) (W := W))
    (P : E →L[ℂ] E) (i : E →L[ℂ] W) (hi : Function.Injective i)
    (hic : IsCompactOperator i) (b α R C D K : ℝ)
    (hb : 0 < b) (hα : 0 < α) (hR : α < R)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hweak : ∀ n x, ‖i ((P ^ n) x)‖ ≤ K * R ^ n * ‖i x‖)
    (hstrong : ∀ n x, ‖(P ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖) :
    NoResidualAbove (normalizedOperator P b) (α / b) := by
  exact noResidual_of_compact_twoNorm source (normalizedOperator P b) (weakEmbedding i)
    (weakEmbedding_injective i hi) (weakEmbedding_isCompact i hic)
    (α / b) (R / b) C (D * weakScale i) K (div_pos hα hb)
    (normalized_rates_lt α R b hb hR) hC (mul_nonneg hD (weakScale_pos i).le) hK
    (weak_power_bound P i b hb K R hweak)
    (strong_twoNorm_power_bound P i b hb C D α R hstrong)

/-- The actual varying-noise operator constructs the complete KL hypotheses,
including no-residual spectrum from the classical radius criterion. -/
theorem exists_hypotheses_of_varying_noise_classical_radius
    [CompleteSpace E] [CompleteSpace W]
    {Ω : Type*} [MeasurableSpace Ω]
    (source : EssentialRadiusContract (E := E) (W := W))
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
    Tendsto (fun ε => ‖i.comp (P ε - P 0)‖) (𝓝 0) (𝓝 0) →
    ∃ h : Hypotheses (fun ε => normalizedOperator (P ε) scale) (weakEmbedding i),
      h.alpha = ρ / scale ∧ h.weakRate = C₀ / scale ∧ IsCompactOperator (weakEmbedding i) := by
  dsimp only
  intro hlimit
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
  have hres : ∀ ε ≤ window, NoResidualAbove (normalizedOperator (P ε) scale) (ρ / scale) := by
    intro ε hε
    exact noResidual_of_normalized_raw_bounds source (P ε) i hi hic scale ρ C₀ Cs Cw 1
      (zero_lt_one.trans_le hscale) hρ hρC₀ hCs hCw zero_le_one
      (hweakP ε hε) (hstrong ε hε)
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
