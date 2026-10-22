module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ReindexedCanonicalChain
public import ConditionedStochasticStabilityHyperbolic.Spectral.HomeomorphicEigenproduct

/-! Spectral data and the constructed eigenproduct of the actual reindexed
absorbing chain. This is used for the literal closed product collar. -/

@[expose] public noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ReindexedCanonicalChain
open LeanShared

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y]
  (e : X ≃ₜ Y) (C : AbsorbingMarkovChains.CanonicalChain Y)
  (sf : HasStrongFellerKernel C)
  (d : RankOneSpectralData (strongFellerTransferOperator C sf) (1 : Y →ᵇ ℝ))

theorem positive (D : AbsorbingMarkovChains.CanonicalChain X)
    (sd : HasStrongFellerKernel D) (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ strongFellerTransferOperator D sd f x := by
  intro x
  rw [strongFellerTransferOperator_represents]
  exact integral_nonneg hf

theorem intertwines :
    (strongFellerTransferOperator C sf).comp
      (HomeomorphicGapTransport.pull ⟨e.symm, e.symm.continuous⟩) =
    (HomeomorphicGapTransport.pull ⟨e.symm, e.symm.continuous⟩).comp
      (strongFellerTransferOperator (chain e C) (strongFeller e C sf)) :=
  HomeomorphicGapTransport.intertwining e (chain e C).killedTransition C.killedTransition
    (strongFellerTransferOperator (chain e C) (strongFeller e C sf))
    (strongFellerTransferOperator C sf)
    (strongFellerTransferOperator_represents (chain e C) (strongFeller e C sf))
    (strongFellerTransferOperator_represents C sf) (kernel_pushforward e C)

def spectralData : RankOneSpectralData
    (strongFellerTransferOperator (chain e C) (strongFeller e C sf)) (1 : X →ᵇ ℝ) :=
  HomeomorphicGapTransport.transport e _ _ d (intertwines e C sf)

@[simp] theorem spectralData_eigenvector (x : X) :
    (spectralData e C sf d).eigenvector x = d.eigenvector (e x) := rfl

variable [CompactSpace X] [CompactSpace Y]

/-- The Riesz eigenproduct is the actual inverse-coordinate marginal. -/
theorem spectralData_product :
    eigenvectorMeasure
      ((spectralData e C sf d).eigenmeasure (positive (chain e C) (strongFeller e C sf)))
      (spectralData e C sf d).eigenvector =
    (eigenvectorMeasure (d.eigenmeasure (positive C sf)) d.eigenvector).map e.symm :=
  HomeomorphicGapTransport.transport_eigenproduct e _ _ d (intertwines e C sf)
    (positive (chain e C) (strongFeller e C sf)) (positive C sf)

end ConditionedStochasticStabilityHyperbolic.ReindexedCanonicalChain
