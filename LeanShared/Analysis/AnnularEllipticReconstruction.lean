module
public import LeanShared.Analysis.AnnularEllipticSymbol
import Mathlib.Tactic.Ring

/-! The constructed annular elliptic symbol transfers every finite Laplacian
power onto the test function in the actual physical Fourier block. -/
public noncomputable section
open scoped SchwartzMap FourierTransform
namespace LeanShared.AnnularEllipticSymbol
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem scaled_norm (ξ : E) :
    -((‖(2*Real.pi) • ξ‖:ℂ)^2) =
      -((2*(Real.pi:ℂ))^2)*((‖ξ‖:ℂ)^2) := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring

theorem reconstruct (σ : 𝓢(E,ℂ)) (support : HasCompactSupport σ)
    (ε : ℝ) (positive : 0 < ε) (collar : ∀ ξ, ‖ξ‖ < ε → σ ξ=0)
    (n : ℕ) (f : 𝓢(E,ℂ)) :
    ConeFourierBlocks.block (symbol σ support ε positive collar n)
      (FourierSchwartzLaplacian.power n f) = ConeFourierBlocks.block σ f := by
  have transform : 𝓕 (ConeFourierBlocks.block (symbol σ support ε positive collar n)
      (FourierSchwartzLaplacian.power n f))=𝓕 (ConeFourierBlocks.block σ f) := by
    ext ξ
    rw [ConeFourierBlocks.fourier_block,FourierSchwartzLaplacian.power_fourier,
      ConeFourierBlocks.fourier_block,← scaled_norm ξ,← mul_assoc,multiply]
  have invert := congrArg (𝓕⁻ : 𝓢(E,ℂ) → 𝓢(E,ℂ)) transform
  simpa only [FourierTransform.fourierInv_fourier_eq] using invert
end LeanShared.AnnularEllipticSymbol
