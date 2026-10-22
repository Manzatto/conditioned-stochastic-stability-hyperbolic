module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedBasicProductEquilibrium
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHilbertProductSplitting

public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedActualPotentialEquilibrium
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductPotentialCoboundary
public import LeanShared.Dynamics.CompactCoreProductEquilibrium
public import LeanShared.Dynamics.ContinuousCoreCoboundary

/-! Actual independent equilibrium for the literal product unstable-Jacobian
potential. Pressure/entropy product theory and the metric coboundary are
proved internally, without a product variational source. -/
public noncomputable section
open Set Function Bundle MeasureTheory
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet
variable {E F X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [CompactSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ,E)) ∞ X]
  [MetricSpace Y] [CompactSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ,F)) ∞ Y]
  [RiemannianBundle (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  [RiemannianBundle (TangentSpace (𝓘(ℝ,F)) : Y → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace (𝓘(ℝ,F)) : Y → Type _)]
local instance provedActualBasicProductEquilibriumCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance provedActualBasicProductEquilibriumManifold : IsManifold (𝓘(ℝ,WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] [BorelSpace (X × Y)]
  {T : X ≃ₜ X} {S : Y ≃ₜ Y} {g : X → ℝ} {h : Y → ℝ} {K V : Set X} {L W : Set Y}

theorem BasicData.product_equilibrium_from_actual_data
    (a : BasicData (E := E) T K V) (b : BasicData (E := F) S L W)
    (forwardT : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverseT : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (forwardS : ContMDiff (𝓘(ℝ,F)) (𝓘(ℝ,F)) 1 S)
    (inverseS : ContMDiff (𝓘(ℝ,F)) (𝓘(ℝ,F)) 1 S.symm)
    (continuousG : ContinuousOn g K) (continuousH : ContinuousOn h L)
    (positiveG : ∀ x ∈ K, 0 < g x) (positiveH : ∀ y ∈ L, 0 < h y)
    (c : HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr S) (K ×ˢ L))
    (forwardProduct : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F)))
      (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S))
    (inverseProduct : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F)))
      (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S).symm)
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (stateμ : ThermodynamicDefinitions.IsEquilibriumState T (a.hyperbolic.potential g) K μ)
    (stateν : ThermodynamicDefinitions.IsEquilibriumState S (b.hyperbolic.potential h) L ν) :
    ThermodynamicDefinitions.IsEquilibriumState (T.prodCongr S)
      (c.potential (fun z : X × Y => g z.1*h z.2)) (K ×ˢ L)
      (⟨(μ : Measure X).prod (ν : Measure Y),inferInstance⟩ : ProbabilityMeasure (X × Y)) := by
  let p := ProductSplittingIdentification.of_actual_product a.hyperbolic b.hyperbolic c
    (forwardT.mdifferentiable (by norm_num)) (inverseT.mdifferentiable (by norm_num))
    (forwardS.mdifferentiable (by norm_num)) (inverseS.mdifferentiable (by norm_num))
    forwardProduct inverseProduct
  exact BasicData.product_equilibrium_actual_potential a b forwardT inverseT forwardS inverseS
    continuousG continuousH positiveG positiveH c p forwardProduct inverseProduct μ ν stateμ stateν

end ConditionedStochasticStabilityHyperbolic.Paper
