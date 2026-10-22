module

public import ConditionedStochasticStabilityHyperbolic.Paper.ReindexedProductLocalPoint

/-! The stabilizing-product construction preserves a single probability family.
Its first marginal has the full original-process conclusion at each admissible
parameter, and weak convergence follows by the same continuous projection. -/

public noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BoundedContinuousFunction Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.ReindexedProductLocalFamily
open LeanShared

variable {X Y Z I : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
  [CompactSpace X] [CompactSpace Y] [CompactSpace Z]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [BorelSpace X] [BorelSpace Y] [BorelSpace Z] [SecondCountableTopology Y]

/-- The original probability is the prescribed first marginal; no choice of
new quasi-ergodic probabilities is made when descending the product. -/
theorem point_marginal
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
    LocalConclusions.Point C R core (νxy.map (fun z => (e.symm z).1)) := by
  obtain ⟨ν, hν, hm⟩ := ReindexedProductLocalPoint.exists_point C D CD sf sd scd e
    independent dy c survival dxy νxy product core hcore y support positive R hR
  have heq : ν = νxy.map (fun z => (e.symm z).1) :=
    ProbabilityMeasure.toMeasure_injective hm
  exact heq ▸ hν

omit [CompactSpace X] [CompactSpace Y] [CompactSpace Z]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
/-- The same projection used for the spectral descent also transports weak
convergence, including for arbitrarily varying driving laws. -/
theorem tendsto_marginal (e : (X × Y) ≃ₜ Z) (l : Filter I)
    (ν : I → ProbabilityMeasure Z) (ν₀ : ProbabilityMeasure Z)
    (hν : Tendsto ν l (𝓝 ν₀)) :
    Tendsto (fun ε => (ν ε).map (fun z => (e.symm z).1)) l
      (𝓝 (ν₀.map (fun z => (e.symm z).1))) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous ν ν₀ hν
    (continuous_fst.comp e.symm.continuous)

end ConditionedStochasticStabilityHyperbolic.Paper.ReindexedProductLocalFamily
