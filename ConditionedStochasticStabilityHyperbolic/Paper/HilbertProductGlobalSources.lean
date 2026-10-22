module
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductHG
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductNonwandering

/-! Stronger source front end for the stabilized global problem. Only
ordinary actual product hyperbolicity, dense orbits, fractional calculus
and pressure/equilibrium product theory are supplied. Both product Axiom-A
periodic density and the nonwandering identity are proved internally. -/
@[expose] public noncomputable section
open Set Function Bundle
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet RegularNoise
variable {E F X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
local instance hilbertProductGlobalSourcesLocal1 : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hilbertProductGlobalSourcesLocal2 : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]
  {T : X ≃ₜ X} {S : Y ≃ₜ Y} (D : SpectralDecomposition (E := E) T)
  (auxiliary : BasicData (E := F) S univ univ)
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]


variable {g : X → ℝ} {A : Set X}



variable
  (hyperbolicProduct : ∀ K : Set X, HyperbolicData (E := E) T K →
    HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr S) (K ×ˢ (univ : Set Y)))
  (auxiliaryPeriodic : closure (periodicPts (S : Y → Y)) = (univ : Set Y))
  (denseOrbit : ∀ i, ∃ z ∈ D.core i ×ˢ (univ : Set Y),
    D.core i ×ˢ (univ : Set Y) ⊆ closure (range (orbit (T.prodCongr S) z)))

/-- Product geometry from actual original Axiom-A data, not an assumed
product spectral decomposition or product nonwandering theorem. -/
def ProductDecompositionSources.ofHyperbolicProduct (h : AxiomAData (E := E) T) :
    ProductDecompositionSources (E := E) (F := F) (S := S) D where
  tangent i := hyperbolicProduct (D.core i) (D.basic i).hyperbolic
  denseOrbit := denseOrbit
  nonwandering := ProductNonwandering.nonwandering_product T S h.periodic_dense auxiliaryPeriodic

/-- The strongest global product source does not ask for product Axiom A,
product periodic density, a product graph, retained indices or pressure order.
The pressure/equilibrium facts are ordinary deterministic thermodynamics for
the literal unstable-Jacobian potential of the constructed tangent data. -/
def ProductHGSources.ofHyperbolicProduct (h : HG1 D g A)
    (regularS : FractionalManifoldRegularity.Regular (E := F) (F := F) h.r S)
    (regularInverseS : FractionalManifoldRegularity.Regular (E := F) (F := F) h.r S.symm)
    (mapsRegular : HilbertMapProductRegularity (E := E) (F := F) (X := X) (Y := Y) h.r)
    (weightRegular : HilbertFirstProjectionRegularity (E := E) (F := F) (X := X) (Y := Y) (h.r - 1))
    (pressure : ∀ i, D.core i ⊆ Aᶜ → ((ProductDecompositionSources.ofHyperbolicProduct D
      hyperbolicProduct auxiliaryPeriodic denseOrbit h.axiomA).decomposition D auxiliary).pressure
        (fun z : X × Y => g z.1) i = D.pressure g i)
    (equilibrium : EquilibriumPackage
      (((ProductDecompositionSources.ofHyperbolicProduct D hyperbolicProduct auxiliaryPeriodic
        denseOrbit h.axiomA).decomposition D auxiliary).basic h.dominant).hyperbolic
      (fun z : X × Y => g z.1)) :
    ProductHGSources D auxiliary
      (ProductDecompositionSources.ofHyperbolicProduct D hyperbolicProduct auxiliaryPeriodic
        denseOrbit h.axiomA) h where
  auxiliary_regular := regularS
  auxiliary_inverse_regular := regularInverseS
  map_calculus := mapsRegular
  weight_calculus := weightRegular
  nonwandering_tangent := by
    have heq : nonwanderingSet (T.prodCongr S) = nonwanderingSet T ×ˢ (univ : Set Y) :=
      ProductNonwandering.nonwandering_product T S h.axiomA.periodic_dense auxiliaryPeriodic
    rw [heq]
    exact hyperbolicProduct _ h.axiomA.hyperbolic
  periodic_dense := ProductNonwandering.periodic_dense_product T S
    h.axiomA.periodic_dense auxiliaryPeriodic
  pressure := pressure
  equilibrium := equilibrium

end ConditionedStochasticStabilityHyperbolic.Paper
