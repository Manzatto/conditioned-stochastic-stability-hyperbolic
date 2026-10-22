module
public import ConditionedStochasticStabilityHyperbolic.Paper.GlobalHypotheses
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedRetainedEquilibria
public import ConditionedStochasticStabilityHyperbolic.Global.FiltrationPressureConfinement
public import ConditionedStochasticStabilityHyperbolic.Global.ConstructedRetainedFiltration
public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationGeometry
public import ConditionedStochasticStabilityHyperbolic.Global.PressureFiltrationSource
public import Mathlib.Topology.VectorBundle.Riemannian

/-! The prescribed greedy filtration of HG2, constructed from no cycles and strict absorption,
with every shifted product boundary null for the reference measure. -/

public noncomputable section
open Set MeasureTheory IsManifold Bundle Filter Function
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.ProvedHG2Filtration
open LeanShared HyperbolicBasicSet Global ShiftedFiltrationGeometry
open FiltrationPressureConfinement ActualHG2BasinGeometry
attribute [local instance] Classical.propDecidable
variable {X Y E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  {T : X ≃ₜ X} (D0 : SpectralDecomposition (E := E) T) (g φ : X → ℝ) (A : Set X)
  (h : HG2 D0 g A)
  (σP : Measure (X × Y)) [IsFiniteMeasure σP] [σP.IsOpenPosMeasure]

set_option quotPrecheck false in
local notation "Λ" => retainedCore D0 A
set_option quotPrecheck false in
local notation "G" => greedy D0 g A h (HG2.proved_retained_pressure_finiteness h)
set_option quotPrecheck false in
local notation "ell" => (G).order.length

structure FiltrationData where
  source : AdaptedSource T A Λ ell
  index : source.index = PressureFiltrationSource.reversedVertex (G).order
  boundary : ∀ N i, 0 < i → i ≤ ell →
    σP (frontier (levels T A Λ ell N source i ×ˢ (univ : Set Y))) = 0
  extra : ∀ N (i : Fin ell),
    σP ((closedLayer T A Λ ell N source i \ stratum T A Λ ell N source i)
      ×ˢ (univ : Set Y)) = 0

@[expose] def filtration (strict : MapsTo T (closure A) A) : FiltrationData D0 g A h σP :=
  Classical.choice (by
    obtain ⟨source, index, boundary, extra⟩ := ConstructedRetainedFiltration.exists_source
      D0 g A h (HG2.proved_retained_pressure_finiteness h) strict σP
    exact ⟨⟨source, index, boundary, extra⟩⟩)

end ConditionedStochasticStabilityHyperbolic.Paper.ProvedHG2Filtration
