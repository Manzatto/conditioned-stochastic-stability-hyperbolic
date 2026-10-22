module
public import LeanShared.Analysis.AnnularDualCutoff

/-! The constructed radial dual cutoff preserves the actual pairing with
any annular block, at every positive frequency scale. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace LeanShared.AnnularDualCutoff
open FourierSchwartzKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem absorb (χ : ConeDyadicSymbols.RadialCutoff) (σ : 𝓢(E,ℂ))
    (annulus : ∀ ξ, σ ξ ≠ 0 → 1/2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2)
    (r : ℝ) (positive : 0 < r) (f test : 𝓢(E,ℂ)) :
    (∫ x, ConeFourierBlocks.block (dilateSymbol σ r positive) f x *
      ConeFourierBlocks.block (dilateSymbol (symbol χ) r positive) test x) =
      ∫ x, ConeFourierBlocks.block (dilateSymbol σ r positive) f x * test x := by
  apply FourierBlockTestPairing.absorb
  intro ξ nonzero
  rw [dilateSymbol_apply] at nonzero ⊢
  obtain ⟨lower,upper⟩ := annulus (r⁻¹ • ξ) nonzero
  apply one χ
  · simpa only [smul_neg,norm_neg] using lower
  · simpa only [smul_neg,norm_neg] using upper
end LeanShared.AnnularDualCutoff
