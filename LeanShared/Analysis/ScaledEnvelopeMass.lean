module
public import LeanShared.Analysis.GraphLeafNorm
public import LeanShared.Analysis.HilbertFrequencyPair
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-! The physical spatial majorants have an exactly scale-independent
finite L1 mass. In particular the dyadic volume factors cancel. -/
public noncomputable section
open MeasureTheory
namespace LeanShared.ScaledEnvelopeMass
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem envelope_eq_radialWeight (m : ℕ) (x : E) :
    HilbertFrequencyPair.envelope m x = GraphLeafNorm.radialWeight (m : ℝ) x := by
  simp only [HilbertFrequencyPair.envelope, GraphLeafNorm.radialWeight,
    Real.rpow_neg (by positivity : 0 ≤ 1+‖x‖), Real.rpow_natCast]

theorem integrable_envelope (μ : Measure E) [μ.IsAddHaarMeasure] {m : ℕ}
    (dimension : Module.finrank ℝ E < m) :
    Integrable (HilbertFrequencyPair.envelope m : E → ℝ) μ := by
  have functions : (HilbertFrequencyPair.envelope m : E → ℝ) =
      GraphLeafNorm.radialWeight (m : ℝ) := funext (envelope_eq_radialWeight m)
  rw [functions]
  exact GraphLeafNorm.integrable_radialWeight μ (by exact_mod_cast dimension :
    (Module.finrank ℝ E : ℝ) < (m : ℝ))

theorem integral_scaled (μ : Measure E) [μ.IsAddHaarMeasure] (m : ℕ)
    {a : ℝ} (positive : 0 < a) :
    (∫ x, a^(Module.finrank ℝ E)*HilbertFrequencyPair.envelope m (a • x) ∂μ) =
      ∫ x, HilbertFrequencyPair.envelope m x ∂μ := by
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg μ _ a (hR := positive.le)]
  change a^(Module.finrank ℝ E)*((a^(Module.finrank ℝ E))⁻¹*
    (∫ x, HilbertFrequencyPair.envelope m x ∂μ)) = _
  rw [←mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ positive.ne'), one_mul]

theorem lintegral_scaled (μ : Measure E) [μ.IsAddHaarMeasure] {m : ℕ}
    (dimension : Module.finrank ℝ E < m) {a : ℝ} (positive : 0 < a) :
    (∫⁻ x, ENNReal.ofReal (a^(Module.finrank ℝ E)*
      HilbertFrequencyPair.envelope m (a • x)) ∂μ) =
      ENNReal.ofReal (∫ x, HilbertFrequencyPair.envelope m x ∂μ) := by
  have integrable := ((integrable_envelope μ dimension).comp_smul positive.ne').const_mul
    (a^(Module.finrank ℝ E))
  rw [←ofReal_integral_eq_lintegral_ofReal integrable, integral_scaled μ m positive]
  filter_upwards with x
  dsimp [HilbertFrequencyPair.envelope]
  positivity

theorem lintegral_scaled_frequency (μ : Measure E) [μ.IsAddHaarMeasure] {m : ℕ}
    (dimension : Module.finrank ℝ E < m) {a q : ℝ} (positive : 0 < a) (hq : 0 < q) :
    (∫⁻ x, ENNReal.ofReal (a^(Module.finrank ℝ E)*
      HilbertFrequencyPair.envelope m ((q*a) • x)) ∂μ) =
      ENNReal.ofReal ((q^(Module.finrank ℝ E))⁻¹)*
        ENNReal.ofReal (∫ x, HilbertFrequencyPair.envelope m x ∂μ) := by
  have scalar (x : E) : a^(Module.finrank ℝ E)*
      HilbertFrequencyPair.envelope m ((q*a) • x) =
      (q^(Module.finrank ℝ E))⁻¹*((q*a)^(Module.finrank ℝ E)*
        HilbertFrequencyPair.envelope m ((q*a) • x)) := by
    rw [mul_pow]
    field_simp
  simp_rw [scalar, ENNReal.ofReal_mul (by positivity : 0 ≤ (q^(Module.finrank ℝ E))⁻¹)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_scaled μ dimension (mul_pos hq positive)]

end LeanShared.ScaledEnvelopeMass
