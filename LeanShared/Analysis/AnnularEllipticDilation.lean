module
public import LeanShared.Analysis.AnnularEllipticReconstruction
import Mathlib.Tactic.FieldSimp

/-! Exact scaling of the constructed elliptic annular parametrix. This yields
the high-frequency gain without an assumed multiplier decay estimate. -/
public noncomputable section
open scoped SchwartzMap FourierTransform
namespace LeanShared.AnnularEllipticSymbol
open FourierSchwartzKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_rescale (r : ℝ) (positive : 0 < r) (ξ : E) :
    (‖ξ‖:ℂ)=(r:ℂ)*(‖r⁻¹ • ξ‖:ℂ) := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr positive),Complex.ofReal_mul,
    Complex.ofReal_inv,← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt positive)),one_mul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem denominator_rescale (r : ℝ) (positive : 0 < r) (ξ : E) (n : ℕ) :
    (-((‖ξ‖:ℂ)^2))^n=(r:ℂ)^(2*n)*(-((‖r⁻¹ • ξ‖:ℂ)^2))^n := by
  conv_lhs => rw [norm_rescale r positive ξ]
  rw [mul_pow,← mul_neg,mul_pow,← pow_mul]

theorem reconstruct_dilated (σ : 𝓢(E,ℂ)) (support : HasCompactSupport σ)
    (ε : ℝ) (positive : 0 < ε) (collar : ∀ ξ, ‖ξ‖ < ε → σ ξ=0)
    (n : ℕ) (r : ℝ) (rpos : 0 < r) (f : 𝓢(E,ℂ)) :
    ConeFourierBlocks.block (dilateSymbol (symbol σ support ε positive collar n) r rpos)
      (FourierSchwartzLaplacian.power n f) =
      (r:ℂ)^(2*n) • ConeFourierBlocks.block (dilateSymbol σ r rpos) f := by
  have transform : 𝓕 (ConeFourierBlocks.block
      (dilateSymbol (symbol σ support ε positive collar n) r rpos)
      (FourierSchwartzLaplacian.power n f)) =
      𝓕 ((r:ℂ)^(2*n) • ConeFourierBlocks.block (dilateSymbol σ r rpos) f) := by
    ext ξ
    simp only [ConeFourierBlocks.fourier_block,FourierSchwartzLaplacian.power_fourier,
      dilateSymbol_apply,FourierTransform.fourier_smul,smul_apply,smul_eq_mul]
    rw [← scaled_norm ξ,denominator_rescale r rpos ((2*Real.pi) • ξ) n]
    calc
      _ = (r:ℂ)^(2*n) * ((symbol σ support ε positive collar n
          (r⁻¹ • ((2*Real.pi) • ξ)) *
          (-((‖r⁻¹ • ((2*Real.pi) • ξ)‖:ℂ)^2))^n) * (𝓕 f) ξ) := by ring
      _ = _ := by rw [multiply]
  have invert := congrArg (𝓕⁻ : 𝓢(E,ℂ) → 𝓢(E,ℂ)) transform
  simpa only [FourierTransform.fourierInv_fourier_eq] using invert
end LeanShared.AnnularEllipticSymbol
