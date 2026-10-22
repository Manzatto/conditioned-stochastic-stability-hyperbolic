module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiverani1999
public import LeanShared.Analysis.FiniteBlockAnnealedEstimates
import Mathlib.Tactic.Linarith

/-! # Producing primary KL hypotheses from actual annealed estimates

The scalar normalization and weak inclusion normalization are performed
internally. Raw weak and two-norm bounds come from the checked finite-block
averaging pipeline. No-residual-spectrum is retained as an explicit classical
spectral premise, independently of relative compactness of the inclusion.
Choosing the operator scale at least one lets the same perturbation modulus
serve the normalized family.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

open LeanShared.TwoNormNormalization

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Actual raw estimates construct the primary-source hypotheses on the
normalized operator family and actual normalized weak inclusion. -/
def hypothesesOfRaw
    (P : ℝ≥0 → E →L[ℂ] E) (i : E →L[ℂ] W) (hi : Function.Injective i)
    (window : ℝ≥0) (hwindow : 0 < window)
    (b ρ M C1 Cs Cw : ℝ) (hb : 1 ≤ b) (hρ : 0 < ρ) (hρb : ρ < b)
    (hρM : ρ < M) (hC1 : 0 < C1) (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw)
    (hweak : ∀ ε ≤ window, ∀ n x, ‖i ((P ε ^ n) x)‖ ≤ C1 * M ^ n * ‖i x‖)
    (hstrong : ∀ ε ≤ window, ∀ n x,
      ‖(P ε ^ n) x‖ ≤ Cs * ρ ^ n * ‖x‖ + Cw * M ^ n * ‖i x‖)
    (hresidual : ∀ ε ≤ window, NoResidualAbove (normalizedOperator (P ε) b) (ρ / b))
    (τ : ℝ≥0 → ℝ≥0) (hτmono : Monotone τ) (hτusc : UpperSemicontinuous τ)
    (hτpos : ∀ ε : ℝ≥0, 0 < ε → 0 < τ ε)
    (hτzero : Tendsto τ (𝓝 0) (𝓝 0))
    (hpert : ∀ ε ≤ window, ‖i.comp (P ε - P 0)‖ ≤ (τ ε : ℝ)) :
    Hypotheses (fun ε => normalizedOperator (P ε) b) (weakEmbedding i) where
  window := window
  window_pos := hwindow
  weak_injective := weakEmbedding_injective i hi
  weak_le_strong := weakEmbedding_norm_le i
  alpha := ρ / b
  alpha_pos := div_pos hρ (zero_lt_one.trans_le hb)
  alpha_lt_one := (div_lt_one (zero_lt_one.trans_le hb)).mpr hρb
  weakRate := M / b
  alpha_lt_weakRate := normalized_rates_lt ρ M b (zero_lt_one.trans_le hb) hρM
  weakConstant := C1
  weakConstant_pos := hC1
  strongConstant := Cs + 1
  strongConstant_pos := by linarith
  errorConstant := Cw * weakScale i + 1
  errorConstant_pos := by
    have hnonneg := mul_nonneg hCw (weakScale_pos i).le
    linarith
  weak_growth := by
    intro ε hε n x
    exact weak_power_bound (P ε) i b (zero_lt_one.trans_le hb) C1 M (hweak ε hε) n x
  twoNorm_growth := by
    intro ε hε n x
    have h := strong_twoNorm_power_bound (P ε) i b (zero_lt_one.trans_le hb)
      Cs Cw ρ M (hstrong ε hε) n x
    apply h.trans
    apply add_le_add
    · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (pow_nonneg (div_nonneg hρ.le (zero_lt_one.trans_le hb).le) n)
    · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (pow_nonneg (div_nonneg (hρ.trans hρM).le (zero_lt_one.trans_le hb).le) n)
  no_residual := hresidual
  modulus := τ
  modulus_monotone := hτmono
  modulus_upperSemicontinuous := hτusc
  modulus_pos := hτpos
  modulus_zero := hτzero
  perturbation := by
    intro ε hε
    rw [norm_normalized_perturbation (P ε) (P 0) i b (zero_lt_one.trans_le hb)]
    have hden : 1 ≤ b * weakScale i := by
      exact one_le_mul_of_one_le_of_one_le hb (weakScale_one_le i)
    exact (div_le_div_of_nonneg_right (hpert ε hε) (zero_lt_one.trans_le hden).le).trans
      (div_le_self (NNReal.coe_nonneg _) hden)

/-- Compactness survives both normalizations; this is relative compactness,
not an assertion that the image of the closed unit ball is closed. -/
theorem normalized_weak_inclusion_compact (i : E →L[ℂ] W) (hi : IsCompactOperator i) :
    IsCompactOperator (weakEmbedding i) := weakEmbedding_isCompact i hi

/-- The actual pointwise averaged family, with uniform independent-noise
word estimates produced from a single block length, satisfies the normalized
primary KL hypotheses. Neither operator-valued measurability nor an
arbitrary-word Lasota--Yorke estimate is assumed. -/
theorem exists_hypotheses_of_actual_annealed_family
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
    (τ : ℝ≥0 → ℝ≥0) (hτmono : Monotone τ) (hτusc : UpperSemicontinuous τ)
    (hτpos : ∀ ε : ℝ≥0, 0 < ε → 0 < τ ε)
    (hτzero : Tendsto τ (𝓝 0) (𝓝 0)) :
    let P := fun ε => LeanShared.AnnealedOperatorBounds.pointwiseAnnealed noise (A ε) (hmeas ε) L (hA ε)
    (∀ ε ≤ window, NoResidualAbove (normalizedOperator (P ε) scale) (ρ / scale)) →
    (∀ ε ≤ window, ‖i.comp (P ε - P 0)‖ ≤ (τ ε : ℝ)) →
    ∃ h : Hypotheses (fun ε => normalizedOperator (P ε) scale) (weakEmbedding i),
      h.alpha = ρ / scale ∧ h.weakRate = C₀ / scale ∧ IsCompactOperator (weakEmbedding i) := by
  dsimp only
  intro hres hpert
  let P := fun ε => LeanShared.AnnealedOperatorBounds.pointwiseAnnealed noise (A ε) (hmeas ε) L (hA ε)
  let Cs := ∑ r ∈ Finset.range N, (L / ρ) ^ r
  let Cw := B / (C₀ ^ N - ρ ^ N)
  have hCs : 0 ≤ Cs := Finset.sum_nonneg (fun _ _ => pow_nonneg (div_nonneg hL hρ.le) _)
  have hden : 0 < C₀ ^ N - ρ ^ N :=
    sub_pos.mpr (pow_lt_pow_left₀ hρC₀ hρ.le hN.ne')
  have hCw : 0 ≤ Cw := div_nonneg hB hden.le
  have hstrong : ∀ ε ≤ window, ∀ n x,
      ‖(P ε ^ n) x‖ ≤ Cs * ρ ^ n * ‖x‖ + Cw * C₀ ^ n * ‖i x‖ := by
    intro ε hε
    exact (LeanShared.FiniteBlockAnnealedEstimates.annealed_twoNorm_bound noise (A ε)
      (hmeas ε) i N hN ρ C₀ M L B hρ hρC₀ hM hMC₀ hL hB (hA ε)
      (hweak ε hε) (hblock ε hε)).2.2
  have hweakP : ∀ ε ≤ window, ∀ n x, ‖i ((P ε ^ n) x)‖ ≤ 1 * C₀ ^ n * ‖i x‖ := by
    intro ε hε n x
    have h := LeanShared.FiniteBlockAnnealedEstimates.annealed_weak_power_bound noise (A ε)
      (hmeas ε) L (hA ε) i M hM (hweak ε hε) n x
    exact h.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM hMC₀ n) (norm_nonneg (i x)))
  let h := hypothesesOfRaw P i hi window hwindow scale ρ C₀ 1 Cs Cw
    hscale hρ hρscale hρC₀ zero_lt_one hCs hCw hweakP hstrong hres
    τ hτmono hτusc hτpos hτzero hpert
  exact ⟨h, rfl, rfl, normalized_weak_inclusion_compact i hic⟩

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
