module

public import ConditionedStochasticStabilityHyperbolic.Spectral.StrongFellerSquareCompact

/-! # Square compactness of the actual raw weighted transfer

The absorbing-chain normalization is a scalar. Its exact cancellation in
conditioned averages does not change power compactness of the raw operator.
-/

@[expose] public noncomputable section
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.StrongFellerSquareCompact
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem raw_square_compact (source : UltraFellerContract (X := X))
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C) (R : ℝ) :
    IsCompactOperator (((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) ^ 2 :
      (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)) := by
  have hc := square_compact source C hSF
  have he : (((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) ^ 2 :
      (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)) =
      ((R : ℂ) * (R : ℂ)) • (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF ^ 2 :
        (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)) := by
    ext f x
    simp only [pow_two, mul_apply_eq_comp, smul_apply, map_smul, smul_smul]
  rw [he]
  change IsCompactOperator (fun f : X →ᵇ ℂ =>
    ((R : ℂ) * (R : ℂ)) • (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF ^ 2) f)
  exact hc.smul ((R : ℂ) * (R : ℂ))

end ConditionedStochasticStabilityHyperbolic.StrongFellerSquareCompact
