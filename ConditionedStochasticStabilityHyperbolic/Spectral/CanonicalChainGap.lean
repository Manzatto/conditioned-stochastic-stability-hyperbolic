module

public import ConditionedStochasticStabilityHyperbolic.Spectral.NoiseSpectralGap
public import ConditionedStochasticStabilityHyperbolic.Spectral.CanonicalGapUniqueness

/-! # The produced raw gap on the actual normalized real killed transfer

Both real transfer constructions use the same kernel integrals. Scalar
normalization preserves the canonical right/left functions, allowing the
local QEM producer's data to enter the retained physical pairing pipeline.
-/

@[expose] public noncomputable section
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.RankOneSpectralData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : E →L[ℝ] E} {one : E}

theorem ofRawNormalization_rate (d : RankOneSpectralData P one)
    (R : ℝ) (hR : 0 < R) {Q : E →L[ℝ] E} (hQ : R⁻¹ • P = Q) :
    (d.ofRawNormalization R hR hQ).rate = R⁻¹ * d.rate := by
  subst Q
  rfl

end ConditionedStochasticStabilityHyperbolic.RankOneSpectralData

namespace ConditionedStochasticStabilityHyperbolic.CanonicalChainGap

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Two actual real transfer constructions coincide, independently of their
implementation of strong-Feller regularity. -/
theorem realTransfer_eq (C : AbsorbingMarkovChains.CanonicalChain X)
    (hSF : HasStrongFellerKernel C) :
    ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF = strongFellerTransferOperator C hSF := by
  ext f x
  rw [ComplexStrongFeller.transferOperator_apply, strongFellerTransferOperator_represents]

/-- Construct the canonical normalized chain gap from the produced raw gap. -/
def normalized (C : AbsorbingMarkovChains.CanonicalChain X)
    (hSF : HasStrongFellerKernel C) (R : ℝ) (hR : 0 < R)
    (d : RankOneSpectralData (R • strongFellerTransferOperator C hSF) (1 : X →ᵇ ℝ)) :
    RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ) :=
  d.ofRawNormalization R hR (by
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hR), one_smul, realTransfer_eq])

@[simp] theorem normalized_mean (C : AbsorbingMarkovChains.CanonicalChain X)
    (hSF : HasStrongFellerKernel C) (R : ℝ) (hR : 0 < R)
    (d : RankOneSpectralData (R • strongFellerTransferOperator C hSF) (1 : X →ᵇ ℝ)) :
    (normalized C hSF R hR d).mean = d.mean :=
  d.ofRawNormalization_mean _ _ _

@[simp] theorem normalized_eigenvector (C : AbsorbingMarkovChains.CanonicalChain X)
    (hSF : HasStrongFellerKernel C) (R : ℝ) (hR : 0 < R)
    (d : RankOneSpectralData (R • strongFellerTransferOperator C hSF) (1 : X →ᵇ ℝ)) :
    (normalized C hSF R hR d).eigenvector = d.eigenvector :=
  d.ofRawNormalization_eigenvector _ _ _

@[simp] theorem normalized_rate (C : AbsorbingMarkovChains.CanonicalChain X)
    (hSF : HasStrongFellerKernel C) (R : ℝ) (hR : 0 < R)
    (d : RankOneSpectralData (R • strongFellerTransferOperator C hSF) (1 : X →ᵇ ℝ)) :
    (normalized C hSF R hR d).rate = R⁻¹ * d.rate :=
  d.ofRawNormalization_rate _ _ _

end ConditionedStochasticStabilityHyperbolic.CanonicalChainGap
