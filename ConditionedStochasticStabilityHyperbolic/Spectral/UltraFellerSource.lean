module

public import ConditionedStochasticStabilityHyperbolic.Spectral.StrongFellerSquareCompact
public import ConditionedStochasticStabilityHyperbolic.Spectral.StrongFellerSquareSubsequence
public import LeanShared.Analysis.BoundedFamilyEquicontinuity

/-! The compact-space ultra-Feller theorem is proved from the literal
strong-Feller property of the actual killed kernel. -/
public section
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.StrongFellerSquareCompact
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem ultraFellerContract : UltraFellerContract (X := X) := by
  intro C sf
  apply LeanShared.BoundedFamilyEquicontinuity.of_subsequences
    (fun f : {f : X →ᵇ ℂ // ‖f‖ ≤ 1} =>
      (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C sf ^ 2) f.val)
  intro u
  obtain ⟨φ,mono,g,convergence⟩ := square_subsequence C sf (fun n => (u n).val)
    (fun n => (u n).property)
  exact ⟨g,φ,mono,convergence⟩

/-- Actual square compactness has no remaining classical source premise. -/
theorem square_compact_proved (C : AbsorbingMarkovChains.CanonicalChain X)
    (sf : HasStrongFellerKernel C) :
    IsCompactOperator (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C sf ^ 2 :
      (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)) := square_compact ultraFellerContract C sf

end ConditionedStochasticStabilityHyperbolic.StrongFellerSquareCompact
