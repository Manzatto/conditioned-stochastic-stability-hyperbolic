module

public import ConditionedStochasticStabilityHyperbolic.Global.EventualScalePrefixSources
public import ConditionedStochasticStabilityHyperbolic.Paper.FixedCubeNoise

/-! The output record of the actual ordinary compact sources: the varying regular duals, the
analytic carriers and the derived eventual-scale prefix sources. -/
public noncomputable section
open Set Filter MeasureTheory ProbabilityTheory IsManifold Bundle
open scoped Topology NNReal Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.CompactClassicalGlobalApplication
open LeanShared Global ShiftedFiltrationGeometry FiltrationPressureConfinement

instance compactLayer {M I : Type*} [MetricSpace M] [CompactSpace M]
    (T : M ≃ₜ M) (A : Set M) (Λ : I → Set M) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (i : Fin ℓ) : CompactSpace (closedLayer T A Λ ℓ N D i) :=
  isCompact_iff_compactSpace.mp (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

end ConditionedStochasticStabilityHyperbolic.Paper.CompactClassicalGlobalApplication

namespace ConditionedStochasticStabilityHyperbolic.Paper.CompactClassicalPrefixSources
open LeanShared Global ShiftedFiltrationGeometry FiltrationPressureConfinement
open LeanShared.ControlledPlaqueClosure
universe uM uE uI uControl uZ uZret uCore uH uMid uW

/-- The source's varying regular duals and all analytic carriers are outputs.
The explicit structure fixes their universes before any actual model is
specialized; it is not a hypothesis of a main theorem. -/
structure Produced
    {M : Type uM} {I : Type uI} {ι : Type uControl} [MetricSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Fintype ι]
    (T : M ≃ₜ M) (A : Set M) (hA : IsOpen A) (Λ : I → Set M) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (k : ℕ) (hk : k ≤ ℓ) (j : Fin ℓ) (hjk : j.val < k)
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain M) where
  Z : Type uZ
  [zNormed : NormedAddCommGroup Z]
  [zScalar : NormedSpace ℂ Z]
  Zret : Type uZret
  [retNormed : NormedAddCommGroup Zret]
  [retScalar : NormedSpace ℂ Zret]
  Core : Type uCore
  [coreNormed : NormedAddCommGroup Core]
  [coreScalar : NormedSpace ℂ Core]
  sf : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, HasStrongFellerKernel (C ε)
  sources : EventualScalePrefixSources.Sources.{uM, uI, uControl, uControl, uZ, uZret, uCore, uH, uMid, uW}
    (Ξ := RegularNoise.FixedControl (ι := ι)) (Ω := RegularNoise.FixedControl (ι := ι))
    (Z := Z) (Zret := Zret) (Core := Core) T A hA Λ ℓ N D k hk j hjk C sf

attribute [instance] Produced.zNormed Produced.zScalar Produced.retNormed
  Produced.retScalar Produced.coreNormed Produced.coreScalar

end ConditionedStochasticStabilityHyperbolic.Paper.CompactClassicalPrefixSources
