module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHilbertProductEquilibrium
public import ConditionedStochasticStabilityHyperbolic.Paper.Hypotheses
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
local instance provedHLProductVariationalCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance provedHLProductVariationalManifold : IsManifold (𝓘(ℝ,WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] [BorelSpace (X × Y)]
  {T : X ≃ₜ X} {S : Y ≃ₜ Y} {g : X → ℝ} {K V : Set X} {L W : Set Y}


theorem HL.product_variational_actual_phi
    (a : HL (E := E) T g K V) (b : HL (E := F) S (fun _ => 1) L W)
    (c : HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr S) (K ×ˢ L))
    (p : ProductSplittingIdentification a.basic.hyperbolic b.basic.hyperbolic c)
    (forwardProduct : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F)))
      (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S))
    (inverseProduct : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F)))
      (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S).symm)
    (φ : X → ℝ) (coreAgree : EqOn g (fun x => Real.exp (φ x)) K)
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (stateμ : ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => φ x-Real.log (a.basic.hyperbolic.unstableJacobian x)) K μ)
    (stateν : ThermodynamicDefinitions.IsEquilibriumState S
      (fun y => (0 : ℝ)-Real.log (b.basic.hyperbolic.unstableJacobian y)) L ν) :
    ThermodynamicDefinitions.IsEquilibriumState (T.prodCongr S)
      (fun z : X × Y => φ z.1-Real.log (c.unstableJacobian z)) (K ×ˢ L)
      (⟨(μ : Measure X).prod (ν : Measure Y),inferInstance⟩ : ProbabilityMeasure (X × Y)) := by
  let ah : BasicAnalyticData (E := E) T g K V := {
    r := a.r, regularity_gt_one := a.regularity_gt_one,
    map_regular := a.map_regular, inverse_regular := a.inverse_regular,
    basic := a.basic, weight_regular := a.weight_regular,
    weight_nonnegative := a.weight_nonnegative, weight_supported := a.weight_supported,
    weight_positive := a.weight_positive }
  let bh : BasicAnalyticData (E := F) S (fun _ => 1) L W := {
    r := b.r, regularity_gt_one := b.regularity_gt_one,
    map_regular := b.map_regular, inverse_regular := b.inverse_regular,
    basic := b.basic, weight_regular := b.weight_regular,
    weight_nonnegative := b.weight_nonnegative, weight_supported := b.weight_supported,
    weight_positive := b.weight_positive }
  have sameX : EqOn (a.basic.hyperbolic.potential g)
      (fun x => φ x-Real.log (a.basic.hyperbolic.unstableJacobian x)) K := by
    intro x hx
    simp only [HyperbolicData.potential,coreAgree hx,Real.log_exp]
  have invariantX : MapsTo T K K := fun x hx => by
    rw [←a.basic.hyperbolic.invariant]
    exact mem_image_of_mem _ hx
  have actualμ := (ThermodynamicDefinitions.isEquilibriumState_iff_of_eqOn invariantX sameX μ).mpr stateμ
  have actualν : ThermodynamicDefinitions.IsEquilibriumState S (b.basic.hyperbolic.potential (fun _ => 1)) L ν := by
    have same : b.basic.hyperbolic.potential (fun _ => 1) =
        (fun y => (0 : ℝ)-Real.log (b.basic.hyperbolic.unstableJacobian y)) := by
      funext y
      change Real.log (1 : ℝ)-_=0-_
      rw [Real.log_one]
    rw [same]
    exact stateν
  have made := ah.product_equilibrium_actual_potential bh c p forwardProduct inverseProduct μ ν actualμ actualν
  have sameProduct : EqOn (c.potential (fun z : X × Y => g z.1*(1 : ℝ)))
      (fun z => φ z.1-Real.log (c.unstableJacobian z)) (K ×ˢ L) := by
    intro z hz
    simp only [HyperbolicData.potential,mul_one,coreAgree hz.1,Real.log_exp]
  exact (ThermodynamicDefinitions.isEquilibriumState_iff_of_eqOn
    (fun z hz => by rw [←c.invariant]; exact mem_image_of_mem _ hz) sameProduct _).mp made

end ConditionedStochasticStabilityHyperbolic.Paper
