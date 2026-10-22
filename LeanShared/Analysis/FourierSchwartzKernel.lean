module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import LeanShared.Analysis.SchwartzKernelBounds
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The manuscript's inverse Fourier kernel as a genuine Schwartz map

Mathlib uses `exp(2π i ⟨ξ,x⟩)` for the inverse transform. The manuscript uses
`(2π)^(-d) ∫ exp(i ⟨x,ξ⟩) symbol(ξ) dξ`. We explicitly rescale the inverse
transform argument by `(2π)⁻¹` and its value by `(2π)^(-d)`.

Smoothness and compact support of a multiplier are the symbol inputs. Actual
angular cone cutoffs and radial dyadic symbol construction are not asserted.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff

namespace LeanShared.FourierSchwartzKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def inverseArgumentScale : E ≃L[ℝ] E :=
  (LinearEquiv.smulOfNeZero ℝ E ((2 * Real.pi)⁻¹)
    (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))).toContinuousLinearEquiv

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem inverseArgumentScale_apply (x : E) :
    inverseArgumentScale x = (2 * Real.pi)⁻¹ • x := rfl

/-- The manuscript normalization, represented without a real-power ambiguity. -/
def normalization : ℝ := ((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem normalization_pos : 0 < normalization (E := E) := by
  unfold normalization
  exact inv_pos.mpr (pow_pos (mul_pos (by norm_num) Real.pi_pos) _)

/-- A genuinely Schwartz inverse-transform kernel with the manuscript convention. -/
def kernel (σ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  (normalization (E := E) : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ inverseArgumentScale (𝓕⁻ σ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The scaling cancels the `2π` in Mathlib's phase exactly. -/
theorem phase_rescaling (x ξ : E) :
    2 * Real.pi * inner ℝ ξ ((2 * Real.pi)⁻¹ • x) = inner ℝ x ξ := by
  rw [real_inner_smul_right, real_inner_comm]
  rw [mul_inv_cancel_left₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero)]

/-- Exact inverse Fourier integral, including the manuscript's scalar normalization. -/
theorem kernel_apply (σ : 𝓢(E, ℂ)) (x : E) :
    kernel σ x = (normalization (E := E) : ℂ) *
      ∫ ξ : E, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * σ ξ := by
  change (normalization (E := E) : ℂ) *
    (𝓕⁻ σ) (inverseArgumentScale x) = _
  rw [inverseArgumentScale_apply]
  have hf : (𝓕⁻ σ) ((2 * Real.pi)⁻¹ • x) =
      ∫ ξ : E, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * σ ξ := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    apply integral_congr_ae
    exact ae_of_all _ fun ξ => by
      change Complex.exp ((2 * Real.pi * inner ℝ ξ ((2 * Real.pi)⁻¹ • x) : ℝ) * Complex.I) * σ ξ = _
      rw [phase_rescaling, mul_comm (inner ℝ x ξ : ℂ) Complex.I]
  rw [hf]

theorem kernel_integrable (σ : 𝓢(E, ℂ)) : Integrable (kernel σ) := (kernel σ).integrable

/-- An actual compactly supported smooth multiplier is an actual Schwartz symbol. -/
def symbol (m : E → ℂ) (hcompact : HasCompactSupport m) (hsmooth : ContDiff ℝ ∞ m) : 𝓢(E, ℂ) :=
  hcompact.toSchwartzMap hsmooth

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem symbol_apply (m : E → ℂ) (hcompact : HasCompactSupport m)
    (hsmooth : ContDiff ℝ ∞ m) (ξ : E) : symbol m hcompact hsmooth ξ = m ξ := rfl

/-- The fixed component kernel is produced from the actual smooth symbol. -/
def fromSymbol (m : E → ℂ) (hcompact : HasCompactSupport m)
    (hsmooth : ContDiff ℝ ∞ m) : 𝓢(E, ℂ) := kernel (symbol m hcompact hsmooth)

theorem fromSymbol_apply (m : E → ℂ) (hcompact : HasCompactSupport m)
    (hsmooth : ContDiff ℝ ∞ m) (x : E) :
    fromSymbol m hcompact hsmooth x = (((2 * Real.pi) ^ Module.finrank ℝ E)⁻¹ : ℂ) *
      ∫ ξ : E, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * m ξ := by
  simpa only [fromSymbol, normalization, symbol_apply, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_ofNat] using
    kernel_apply (symbol m hcompact hsmooth) x

/-- Inverse dilation of an actual symbol, again as an actual Schwartz map. -/
def dilateSymbol (σ : 𝓢(E, ℂ)) (r : ℝ) (hr : 0 < r) : 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ E r⁻¹ (inv_ne_zero (ne_of_gt hr))).toContinuousLinearEquiv σ

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem dilateSymbol_apply (σ : 𝓢(E, ℂ)) (r : ℝ) (hr : 0 < r) (ξ : E) :
    dilateSymbol σ r hr ξ = σ (r⁻¹ • ξ) := rfl

omit [MeasurableSpace E] [BorelSpace E] in
theorem dilateSymbol_hasCompactSupport (σ : 𝓢(E, ℂ)) (hσ : HasCompactSupport (σ : E → ℂ))
    (r : ℝ) (hr : 0 < r) : HasCompactSupport (dilateSymbol σ r hr : E → ℂ) :=
  hσ.comp_homeomorph
    (LinearEquiv.smulOfNeZero ℝ E r⁻¹ (inv_ne_zero (ne_of_gt hr))).toContinuousLinearEquiv.toHomeomorph

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem inner_dilation_cancel (r : ℝ) (hr : r ≠ 0) (x ξ : E) :
    inner ℝ (r • x) (r⁻¹ • ξ) = inner ℝ x ξ := by
  rw [real_inner_smul_left, real_inner_smul_right, mul_inv_cancel_left₀ hr]

/-- The exact kernel dilation formula with the manuscript Fourier convention. -/
theorem kernel_dilateSymbol (σ : 𝓢(E, ℂ)) (r : ℝ) (hr : 0 < r) (x : E) :
    kernel (dilateSymbol σ r hr) x = (r ^ Module.finrank ℝ E) • kernel σ (r • x) := by
  borelize E
  rw [kernel_apply, kernel_apply]
  simp only [dilateSymbol_apply]
  have heq : (∫ ξ : E, Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) * σ (r⁻¹ • ξ)) =
      (r ^ Module.finrank ℝ E) •
        ∫ ξ : E, Complex.exp (Complex.I * (inner ℝ (r • x) ξ : ℂ)) * σ ξ := by
    calc
      _ = ∫ ξ : E, Complex.exp (Complex.I * (inner ℝ (r • x) (r⁻¹ • ξ) : ℂ)) * σ (r⁻¹ • ξ) := by
        apply integral_congr_ae
        exact ae_of_all _ fun ξ => by simp only [inner_dilation_cancel r (ne_of_gt hr)]
      _ = _ := Measure.integral_comp_inv_smul_of_nonneg volume
        (fun ξ : E => Complex.exp (Complex.I * (inner ℝ (r • x) ξ : ℂ)) * σ ξ) hr.le
  rw [heq, mul_smul_comm]

/-- Dilation preserves the actual ambient `L1` kernel norm exactly. -/
theorem integral_norm_kernel_dilateSymbol (σ : 𝓢(E, ℂ)) (r : ℝ) (hr : 0 < r) :
    (∫ x : E, ‖kernel (dilateSymbol σ r hr) x‖) = ∫ x : E, ‖kernel σ x‖ := by
  borelize E
  simp only [kernel_dilateSymbol, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hr.le _)]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg volume (fun x : E => ‖kernel σ x‖) r (hR := hr.le),
    smul_eq_mul, mul_inv_cancel_left₀ (pow_ne_zero _ (ne_of_gt hr))]

end LeanShared.FourierSchwartzKernel
