module
public import LeanShared.Analysis.ConeFourierBlocks
public import LeanShared.Analysis.ConstructedEnlargedConeSymbols

/-! The constructed enlarged multipliers reproduce the actual input
Schwartz blocks exactly; no frequency localization identity is supplied. -/
public noncomputable section
open scoped SchwartzMap FourierTransform
namespace LeanShared.EnlargedConeBlockReproduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem block_reproduces (original enlarged : 𝓢(E,ℂ))
    (identity : ∀ ξ, original ξ*enlarged ξ = original ξ) (f : 𝓢(E,ℂ)) :
    ConeFourierBlocks.block enlarged (ConeFourierBlocks.block original f) =
      ConeFourierBlocks.block original f := by
  have transformed : 𝓕 (ConeFourierBlocks.block enlarged (ConeFourierBlocks.block original f)) =
      𝓕 (ConeFourierBlocks.block original f) := by
    ext ξ
    simp_rw [ConeFourierBlocks.fourier_block]
    rw [←mul_assoc, mul_comm (enlarged ((2*Real.pi) • ξ)), identity]
  have actual := congrArg (fun h : 𝓢(E,ℂ) => 𝓕⁻ h) transformed
  simpa using actual

theorem constructed_reproduction {Cp Cm : Set E}
    (cutoffs : ConstructedEnlargedConeSymbols.Cutoffs Cp Cm)
    (χ : ConeDyadicSymbols.RadialCutoff) (j : ℕ × Bool) (f : 𝓢(E,ℂ)) :
    ConeFourierBlocks.block
      (EnlargedConeDyadicSymbols.symbols χ cutoffs.enlarged cutoffs.smooth j)
      (ConeFourierBlocks.block (ConeDyadicSymbols.symbols χ cutoffs.original j) f) =
      ConeFourierBlocks.block (ConeDyadicSymbols.symbols χ cutoffs.original j) f :=
  block_reproduces _ _ (cutoffs.multiplier_identity χ j) f

end LeanShared.EnlargedConeBlockReproduction
