module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProductLocalPoint
public import ConditionedStochasticStabilityHyperbolic.Spectral.ConstantSurvivalRankOne

/-! An unabsorbed auxiliary factor needs no supplied positivity region for
its eigenvector: constant survival canonically makes that vector one. -/

public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.ProductConstantLocalPoint
open LeanShared

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y] [SecondCountableTopology Y]

/-- Full local conclusions descend using constant auxiliary survival. There
is no positivity hypothesis about its chosen spectral eigenvector. -/
theorem exists_point
    (C : AbsorbingMarkovChains.CanonicalChain X)
    (D : AbsorbingMarkovChains.CanonicalChain Y)
    (CD : AbsorbingMarkovChains.CanonicalChain (X × Y))
    (sf : HasStrongFellerKernel C) (sd : HasStrongFellerKernel D)
    (scd : HasStrongFellerKernel CD)
    (independent : ∀ x y, CD.killedTransition (x, y) =
      (C.killedTransition x).prod (D.killedTransition y))
    (dy : RankOneSpectralData (strongFellerTransferOperator D sd) (1 : Y →ᵇ ℝ))
    (c : ℝ) (survival : strongFellerTransferOperator D sd 1 = c • (1 : Y →ᵇ ℝ))
    (dxy : RankOneSpectralData (strongFellerTransferOperator CD scd) (1 : X × Y →ᵇ ℝ))
    (νxy : ProbabilityMeasure (X × Y))
    (product : (νxy : Measure (X × Y)) = eigenvectorMeasure
      (dxy.eigenmeasure (fun f hf z => by
        rw [strongFellerTransferOperator_represents]
        exact integral_nonneg hf)) dxy.eigenvector)
    (core : Set X) (hcore : core.Nonempty) (y : Y)
    (support : ∀ x ∈ core, (x, y) ∈ (νxy : Measure (X × Y)).support)
    (positive : ∀ x ∈ core, 0 < dxy.eigenvector (x, y))
    (R : ℝ) (hR : 0 < R) :
    ∃ ν : ProbabilityMeasure X, LocalConclusions.Point C R core ν ∧
      (ν : Measure X) = (νxy : Measure (X × Y)).map Prod.fst := by
  apply ProductLocalPoint.exists_point C D CD sf sd scd independent
    (dy.normalizeOne c survival) dxy νxy product core hcore y _ support positive R hR
  change (0 : ℝ) < 1
  exact zero_lt_one

end ConditionedStochasticStabilityHyperbolic.Paper.ProductConstantLocalPoint
