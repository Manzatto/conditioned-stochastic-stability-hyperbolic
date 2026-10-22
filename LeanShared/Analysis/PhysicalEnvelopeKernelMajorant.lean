module
public import LeanShared.Analysis.HilbertFrequencyPair
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! The actual real physical-kernel estimate implies the normalized positive
convolution majorant on a genuine diffeomorphism window. Agreement is needed
only on the compact integration region, not outside the chart. -/
public noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LeanShared.PhysicalEnvelopeKernelMajorant
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
theorem bound (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (m : ℕ) {a b q c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (G F : E → E) (continuousG : Continuous G) {L O : Set E}
    (compactL : IsCompact L) (inside : L ⊆ O) (same : EqOn G F L)
    (kernel : E → E → ℂ) (x y : E)
    (estimate : ‖kernel x y‖ ≤ c*(a^(Module.finrank ℝ E)*b^(Module.finrank ℝ E))*
      (∫ w in L, HilbertFrequencyPair.envelope m ((q*a) • (x-w))*
        HilbertFrequencyPair.envelope m ((q*b) • (G w-y)) ∂μ)) :
    ‖kernel x y‖ₑ ≤ ENNReal.ofReal c*(∫⁻ w,
      ENNReal.ofReal (a^(Module.finrank ℝ E)*HilbertFrequencyPair.envelope m ((q*a) • (x-w)))*
      O.indicator (fun _ => 1) w*
      ENNReal.ofReal (b^(Module.finrank ℝ E)*HilbertFrequencyPair.envelope m ((q*b) • (F w-y))) ∂μ) := by
  let p : E → ℝ := fun w => HilbertFrequencyPair.envelope m ((q*a) • (x-w))*
    HilbertFrequencyPair.envelope m ((q*b) • (G w-y))
  have continuousEnvelope : Continuous (HilbertFrequencyPair.envelope m : E → ℝ) := by
    apply Continuous.inv₀ (by fun_prop)
    intro z
    positivity
  have continuousP : Continuous p := by
    exact (continuousEnvelope.comp (continuous_const.smul (continuous_const.sub continuous_id))).mul
      (continuousEnvelope.comp (continuous_const.smul (continuousG.sub continuous_const)))
  have nonnegative (w : E) : 0 ≤ p w := by
    dsimp [p, HilbertFrequencyPair.envelope]
    positivity
  have scaled : ENNReal.ofReal (a^(Module.finrank ℝ E)*b^(Module.finrank ℝ E)*
      (∫ w in L, p w ∂μ)) = ∫⁻ w in L,
      ENNReal.ofReal (a^(Module.finrank ℝ E)*HilbertFrequencyPair.envelope m ((q*a) • (x-w)))*
      ENNReal.ofReal (b^(Module.finrank ℝ E)*HilbertFrequencyPair.envelope m ((q*b) • (G w-y))) ∂μ := by
    rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)),
      ofReal_integral_eq_lintegral_ofReal (continuousP.continuousOn.integrableOn_compact compactL)
        (Filter.Eventually.of_forall nonnegative), ←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro w
    rw [←ENNReal.ofReal_mul (mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)),
      ←ENNReal.ofReal_mul (mul_nonneg (pow_nonneg ha _) (by
        dsimp [HilbertFrequencyPair.envelope]; positivity))]
    congr 1
    dsimp [p]
    ring
  have pointwise := ENNReal.ofReal_le_ofReal estimate
  rw [ofReal_norm] at pointwise
  calc
    _ ≤ ENNReal.ofReal (c*(a^(Module.finrank ℝ E)*b^(Module.finrank ℝ E)*(∫ w in L,p w ∂μ))) := by
      simpa only [mul_assoc, p] using pointwise
    _ = ENNReal.ofReal c*(∫⁻ w in L,
        ENNReal.ofReal (a^(Module.finrank ℝ E)*HilbertFrequencyPair.envelope m ((q*a) • (x-w)))*
        ENNReal.ofReal (b^(Module.finrank ℝ E)*HilbertFrequencyPair.envelope m ((q*b) • (G w-y))) ∂μ) := by
      rw [ENNReal.ofReal_mul hc, scaled]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ bot_le
      rw [←lintegral_indicator compactL.measurableSet]
      apply lintegral_mono
      intro w
      by_cases member : w ∈ L
      · simp only [indicator_of_mem member, indicator_of_mem (inside member), mul_one]
        rw [same member]
      · simp only [indicator_of_notMem member]
        exact bot_le

end LeanShared.PhysicalEnvelopeKernelMajorant
