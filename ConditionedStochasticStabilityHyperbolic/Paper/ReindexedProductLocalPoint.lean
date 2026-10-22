module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProductConstantLocalPoint
public import ConditionedStochasticStabilityHyperbolic.Spectral.ReindexedSpectralData

/-! Descend from a product theorem stated on the literal closed-collar
subtype. The auxiliary state identification, process and eigenproduct are
constructed before projecting to the original live state. -/

public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.ReindexedProductLocalPoint
open LeanShared

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
  [CompactSpace X] [CompactSpace Y] [CompactSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [BorelSpace X] [BorelSpace Y] [BorelSpace Z] [SecondCountableTopology Y]

/-- Full local conclusions on the original factor follow from the actual
closed-product process. No spectral conclusion on that factor is a premise. -/
theorem exists_point
    (C : AbsorbingMarkovChains.CanonicalChain X)
    (D : AbsorbingMarkovChains.CanonicalChain Y)
    (CD : AbsorbingMarkovChains.CanonicalChain Z)
    (sf : HasStrongFellerKernel C) (sd : HasStrongFellerKernel D)
    (scd : HasStrongFellerKernel CD) (e : (X × Y) ≃ₜ Z)
    (independent : ∀ x y, (CD.killedTransition (e (x, y))).map e.symm =
      (C.killedTransition x).prod (D.killedTransition y))
    (dy : RankOneSpectralData (strongFellerTransferOperator D sd) (1 : Y →ᵇ ℝ))
    (c : ℝ) (survival : strongFellerTransferOperator D sd 1 = c • (1 : Y →ᵇ ℝ))
    (dxy : RankOneSpectralData (strongFellerTransferOperator CD scd) (1 : Z →ᵇ ℝ))
    (νxy : ProbabilityMeasure Z)
    (product : (νxy : Measure Z) = eigenvectorMeasure
      (dxy.eigenmeasure (fun f hf z => by
        rw [strongFellerTransferOperator_represents]
        exact integral_nonneg hf)) dxy.eigenvector)
    (core : Set X) (hcore : core.Nonempty) (y : Y)
    (support : ∀ x ∈ core, e (x, y) ∈ (νxy : Measure Z).support)
    (positive : ∀ x ∈ core, 0 < dxy.eigenvector (e (x, y)))
    (R : ℝ) (hR : 0 < R) :
    ∃ ν : ProbabilityMeasure X, LocalConclusions.Point C R core ν ∧
      (ν : Measure X) = (νxy : Measure Z).map (fun z => (e.symm z).1) := by
  let CP := ReindexedCanonicalChain.chain e CD
  let sp := ReindexedCanonicalChain.strongFeller e CD scd
  let dp := ReindexedCanonicalChain.spectralData e CD scd dxy
  let νp : ProbabilityMeasure (X × Y) := νxy.map e.symm
  have hind : ∀ x y, CP.killedTransition (x, y) =
      (C.killedTransition x).prod (D.killedTransition y) := by
    intro x y
    rw [ReindexedCanonicalChain.killed]
    exact independent x y
  have hp : (νp : Measure (X × Y)) = eigenvectorMeasure
      (dp.eigenmeasure (fun f hf z => by
        rw [strongFellerTransferOperator_represents]
        exact integral_nonneg hf)) dp.eigenvector := by
    change (νxy : Measure Z).map e.symm = _
    rw [product]
    exact (ReindexedCanonicalChain.spectralData_product e CD scd dxy).symm
  have hs : ∀ x ∈ core, (x, y) ∈ (νp : Measure (X × Y)).support := by
    intro x hx
    exact (HomeomorphicGapTransport.mem_support_inverse_map e (νxy : Measure Z) (x, y)).mpr
      (support x hx)
  have hg : ∀ x ∈ core, 0 < dp.eigenvector (x, y) := by
    intro x hx
    exact positive x hx
  obtain ⟨ν, hν, hmap⟩ := ProductConstantLocalPoint.exists_point C D CP sf sd sp hind
    dy c survival dp νp hp core hcore y hs hg R hR
  refine ⟨ν, hν, ?_⟩
  rw [hmap]
  change ((νxy : Measure Z).map e.symm).map Prod.fst = _
  rw [Measure.map_map measurable_fst e.symm.measurable]
  rfl

end ConditionedStochasticStabilityHyperbolic.Paper.ReindexedProductLocalPoint
