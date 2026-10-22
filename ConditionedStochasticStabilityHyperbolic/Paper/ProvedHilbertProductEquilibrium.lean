module

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
local instance provedHilbertProductEquilibriumCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance provedHilbertProductEquilibriumManifold : IsManifold (𝓘(ℝ,WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] [BorelSpace (X × Y)]
  {T : X ≃ₜ X} {S : Y ≃ₜ Y} {g : X → ℝ} {h : Y → ℝ} {K V : Set X} {L W : Set Y}

theorem BasicAnalyticData.product_equilibrium_actual_potential
    (a : BasicAnalyticData (E := E) T g K V) (b : BasicAnalyticData (E := F) S h L W)
    (c : HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr S) (K ×ˢ L))
    (p : ProductSplittingIdentification a.basic.hyperbolic b.basic.hyperbolic c)
    (forwardProduct : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F)))
      (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S))
    (inverseProduct : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F)))
      (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S).symm)
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (stateμ : ThermodynamicDefinitions.IsEquilibriumState T (a.basic.hyperbolic.potential g) K μ)
    (stateν : ThermodynamicDefinitions.IsEquilibriumState S (b.basic.hyperbolic.potential h) L ν) :
    ThermodynamicDefinitions.IsEquilibriumState (T.prodCongr S)
      (c.potential (fun z : X × Y => g z.1*h z.2)) (K ×ˢ L)
      (⟨(μ : Measure X).prod (ν : Measure Y),inferInstance⟩ : ProbabilityMeasure (X × Y)) := by
  obtain ⟨cr,crpositive,expansiveT⟩ := a.exists_expansivity_radius
  obtain ⟨cs,cspositive,expansiveS⟩ := b.exists_expansivity_radius
  have independent := ThermodynamicDefinitions.IsEquilibriumState.product_on_compact_cores T S K L
    a.basic.hyperbolic.compact b.basic.hyperbolic.compact
    a.basic.hyperbolic.invariant b.basic.hyperbolic.invariant cr cs crpositive cspositive
    expansiveT expansiveS _ _ a.actual_potential_continuousOn b.actual_potential_continuousOn
    μ ν stateμ stateν
  have an : (1 : ℕ) ≤ ⌊a.r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using a.regularity_gt_one.le)
  have bn : (1 : ℕ) ≤ ⌊b.r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using b.regularity_gt_one.le)
  have aForward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T := a.map_regular.differentiable.of_le (by exact_mod_cast an)
  have aInverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm := a.inverse_regular.differentiable.of_le (by exact_mod_cast an)
  have bForward : ContMDiff (𝓘(ℝ,F)) (𝓘(ℝ,F)) 1 S := b.map_regular.differentiable.of_le (by exact_mod_cast bn)
  have bInverse : ContMDiff (𝓘(ℝ,F)) (𝓘(ℝ,F)) 1 S.symm := b.inverse_regular.differentiable.of_le (by exact_mod_cast bn)
  have same := p.potential_coboundary a.basic.hyperbolic b.basic.hyperbolic c
    (aForward.mdifferentiable (by norm_num)) (aInverse.mdifferentiable (by norm_num))
    (bForward.mdifferentiable (by norm_num)) (bInverse.mdifferentiable (by norm_num))
    forwardProduct inverseProduct g h a.weight_positive b.weight_positive
  apply (ThermodynamicDefinitions.isEquilibriumState_iff_continuous_core_coboundary
    (T.prodCongr S) (K ×ˢ L) c.compact
    (fun z hz => by rw [←c.invariant]; exact mem_image_of_mem _ hz)
    (c.potential (fun z => g z.1*h z.2))
    (fun z => a.basic.hyperbolic.potential g z.1+b.basic.hyperbolic.potential h z.2)
    (fun z => Real.log (p.unstableVolume a.basic.hyperbolic b.basic.hyperbolic c z))
    (p.continuousOn_log_unstableVolume a.basic.hyperbolic b.basic.hyperbolic c) same _).mpr
  exact independent

end ConditionedStochasticStabilityHyperbolic.Paper
