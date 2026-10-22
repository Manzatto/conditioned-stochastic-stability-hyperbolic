module
public import LeanShared.Analysis.ConeFourierBlocks

/-! Actual test pairings for physical Fourier blocks. A reflected dual cutoff
which is one on the block multiplier preserves the pairing exactly. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace LeanShared.FourierBlockTestPairing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem inverse_block (σ f : 𝓢(E,ℂ)) (ξ : E) :
    (𝓕⁻ (ConeFourierBlocks.block σ f)) ξ =
      σ (-(2*Real.pi) • ξ) * (𝓕⁻ f) ξ := by
  change (𝓕 (ConeFourierBlocks.block σ f)) (-ξ) =
    σ (-(2*Real.pi) • ξ) * (𝓕 f) (-ξ)
  rw [ConeFourierBlocks.fourier_block]
  simp only [smul_neg,neg_smul]

theorem pairing (f g : 𝓢(E,ℂ)) :
    (∫ x, f x*g x) = ∫ ξ, (𝓕 f) ξ*(𝓕⁻ g) ξ := by
  have identity := SchwartzMap.integral_fourierInv_mul_eq (𝓕 f) g
  simpa only [FourierTransform.fourierInv_fourier_eq] using identity

theorem absorb (σ χ f g : 𝓢(E,ℂ))
    (cutoff : ∀ ξ, σ ξ ≠ 0 → χ (-ξ)=1) :
    (∫ x, ConeFourierBlocks.block σ f x * ConeFourierBlocks.block χ g x) =
      ∫ x, ConeFourierBlocks.block σ f x * g x := by
  conv_lhs => rw [pairing]
  conv_rhs => rw [pairing]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ => by
    dsimp only
    rw [ConeFourierBlocks.fourier_block,inverse_block]
    by_cases zero : σ ((2*Real.pi) • ξ)=0
    · rw [zero,zero_mul,zero_mul,zero_mul]
    · have value : χ (-(2*Real.pi) • ξ)=1 := by
        simpa only [neg_smul] using cutoff ((2*Real.pi) • ξ) zero
      rw [value,one_mul]
end LeanShared.FourierBlockTestPairing
