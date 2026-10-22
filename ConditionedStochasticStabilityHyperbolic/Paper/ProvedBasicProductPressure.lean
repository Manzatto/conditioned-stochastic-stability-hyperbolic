module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedActualPotentialEquilibrium
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductPotentialCoboundary
public import LeanShared.Dynamics.CompactCoreProductPressure
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
local instance provedBasicProductPressureCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance provedBasicProductPressureManifold : IsManifold (𝓘(ℝ,WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)]
  {T : X ≃ₜ X} {S : Y ≃ₜ Y} {g : X → ℝ} {h : Y → ℝ} {K V : Set X} {L W : Set Y}

theorem BasicData.product_pressure_actual_potential
    (a : BasicData (E := E) T K V) (b : BasicData (E := F) S L W)
    (forwardT : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverseT : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (forwardS : ContMDiff (𝓘(ℝ,F)) (𝓘(ℝ,F)) 1 S)
    (inverseS : ContMDiff (𝓘(ℝ,F)) (𝓘(ℝ,F)) 1 S.symm)
    (continuousG : ContinuousOn g K) (continuousH : ContinuousOn h L)
    (positiveG : ∀ x ∈ K, 0 < g x) (positiveH : ∀ y ∈ L, 0 < h y)
    (c : HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr S) (K ×ˢ L))
    (p : ProductSplittingIdentification a.hyperbolic b.hyperbolic c)
    (forwardProduct : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F)))
      (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S))
    (inverseProduct : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F)))
      (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S).symm)
 :
    LeanShared.ThermodynamicDefinitions.pressure (T.prodCongr S)
      (c.potential (fun z : X × Y => g z.1*h z.2)) (K ×ˢ L)=
    LeanShared.ThermodynamicDefinitions.pressure T (a.hyperbolic.potential g) K+
      LeanShared.ThermodynamicDefinitions.pressure S (b.hyperbolic.potential h) L := by
  obtain ⟨cr,crpositive,expansiveT⟩ := a.exists_expansivity_radius forwardT inverseT
  obtain ⟨cs,cspositive,expansiveS⟩ := b.exists_expansivity_radius forwardS inverseS
  have additive := ThermodynamicDefinitions.pressure_product_on_compact_cores T S K L
    a.hyperbolic.compact b.hyperbolic.compact a.nonempty b.nonempty
    a.hyperbolic.invariant b.hyperbolic.invariant cr cs crpositive cspositive
    expansiveT expansiveS _ _ (a.hyperbolic.continuousOn_potential forwardT (inverseT.mdifferentiable (by norm_num)) g continuousG positiveG)
    (b.hyperbolic.continuousOn_potential forwardS (inverseS.mdifferentiable (by norm_num)) h continuousH positiveH)
  have same := p.potential_coboundary a.hyperbolic b.hyperbolic c
    (forwardT.mdifferentiable (by norm_num)) (inverseT.mdifferentiable (by norm_num))
    (forwardS.mdifferentiable (by norm_num)) (inverseS.mdifferentiable (by norm_num))
    forwardProduct inverseProduct g h positiveG positiveH
  have metric := ThermodynamicDefinitions.pressure_continuous_core_coboundary
    (T.prodCongr S) (K ×ˢ L) c.compact
    (fun z hz => by rw [←c.invariant]; exact mem_image_of_mem _ hz)
    (c.potential (fun z => g z.1*h z.2))
    (fun z => a.hyperbolic.potential g z.1+b.hyperbolic.potential h z.2)
    (fun z => Real.log (p.unstableVolume a.hyperbolic b.hyperbolic c z))
    (p.continuousOn_log_unstableVolume a.hyperbolic b.hyperbolic c) same
  exact metric.trans additive

end ConditionedStochasticStabilityHyperbolic.Paper
