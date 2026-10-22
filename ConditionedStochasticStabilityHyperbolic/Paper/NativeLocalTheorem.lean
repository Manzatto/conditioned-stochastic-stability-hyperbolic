module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeStabilizedLocalLeading
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductWhitneyBound
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHilbertScalarProductRegularity
public import ConditionedStochasticStabilityHyperbolic.Paper.ConcreteToralAuxiliaryAnosov
public import ConditionedStochasticStabilityHyperbolic.Paper.ConcreteToralHLProduct
public import LeanShared.Geometry.SmoothFractionalRegularity
public import LeanShared.Geometry.FractionalScalarMultiplication

/-!
Theorems `thm:qem-local` and `thm:local`. Under HL with isolating neighbourhood
`V`, for every regular noise and laws and every `C^{r-1}` departure weight `w ≥ 0` equal to `g` on
`Λ` and to `e^φ` on `closure V`, the live chain on `closure V` has, for all small positive scales,
the unique quasi-ergodic measures whose limit is the equilibrium state of
`φ - log |det DT|_{E^u}|`, together with gap retention. The stabilizing auxiliary is the concrete
cat map, the product calculus and the product weight regularity are proved, and the analysis
neighbourhood is `V × T²`; no dimension, source, spectral or stability hypothesis is used.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory Bundle Filter
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeLocalTheorem
open LeanShared HyperbolicBasicSet RegularNoise

variable {X E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  {ι : Type} [Fintype ι] {T : X ≃ₜ X} {g : X → ℝ} {Λ V : Set X}

local instance nativeLocalOrdinaryCharts : ChartedSpace (E × ToralCatMap.Model) (X × ToralCatMap.Torus) :=
  prodChartedSpace E X ToralCatMap.Model ToralCatMap.Torus
local instance nativeLocalProductCharts :
    ChartedSpace (WithLp 2 (E × ToralCatMap.Model)) (X × ToralCatMap.Torus) :=
  LinearRechartedManifold.productCharts
local instance nativeLocalProductManifold :
    IsManifold (𝓘(ℝ, WithLp 2 (E × ToralCatMap.Model))) ∞ (X × ToralCatMap.Torus) :=
  LinearRechartedManifold.product_manifold

local instance localCompactClosure (W : Set X) : CompactSpace (closure W) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

omit [MeasurableSpace E] [BorelSpace E] in
/-- Literal local stochastic stability and gap retention (thm:local, thm:qem-local). -/
theorem stability_and_retention (h : HL (E := E) T g Λ V)
    (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
    (w : X → ℝ) (hwRegular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1) w)
    (hw0 : ∀ x, 0 ≤ w x) (agree : EqOn w g Λ)
    (φ : X → ℝ) (weight_exp : ∀ x : closure V, w x.val = Real.exp (φ x.val)) :
    ∃ (hwExp : Continuous (fun x : closure V => Real.exp (φ x.val)))
      (R : ℝ) (hR : 0 < R) (bound : ∀ x : closure V, Real.exp (φ x.val) ≤ R),
      LocalConclusions.Stability P L (closure V) Λ isClosed_closure.measurableSet
        (fun x => Real.exp (φ x.val)) hwExp.measurable R hR bound
        (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) ∧
      LocalConclusions.GapRetention P L (closure V) Λ isClosed_closure.measurableSet
        (fun x => Real.exp (φ x.val)) hwExp.measurable R hR bound := by
  let a := ToralCatMap.auxiliary h.r h.regularity_gt_one
  let _ : MeasurableSpace (WithLp 2 (E × ToralCatMap.Model)) := borel _
  have _ : BorelSpace (WithLp 2 (E × ToralCatMap.Model)) := ⟨rfl⟩
  let _ : RiemannianBundle (TangentSpace (𝓘(ℝ, ConcreteToralHLProduct.Model E))
      (M := X × ConcreteToralHLProduct.Auxiliary)) := ConcreteToralHLProduct.bundle
  have _ : IsContinuousRiemannianBundle (ConcreteToralHLProduct.Model E)
      (TangentSpace (𝓘(ℝ, ConcreteToralHLProduct.Model E)) (M := X × ConcreteToralHLProduct.Auxiliary)) :=
    SmoothMetricBundleClasses.continuous (ConcreteToralHLProduct.metric (E := E) (X := X))
  have hw : Continuous w := hwRegular.differentiable.continuous
  have constantOne : FractionalManifoldRegularity.Regular (E := ToralCatMap.Model) (F := ℝ)
      (h.r - 1) (fun _ : ToralCatMap.Torus => (1 : ℝ)) :=
    FractionalManifoldRegularity.regular_of_smooth contMDiff_const (by linarith [h.regularity_gt_one])
  have productWeight := proved_hilbertScalarProductRegularity (E := E) (F := ToralCatMap.Model)
    (X := X) (Y := ToralCatMap.Torus) (h.r - 1) w (fun _ => 1) hwRegular constantOne
  have smoothProduct : ∀ ζ : X × ToralCatMap.Torus → ℝ,
      ContMDiff (𝓘(ℝ, WithLp 2 (E × ToralCatMap.Model))) (𝓘(ℝ)) ∞ ζ →
      tsupport ζ ⊆ V ×ˢ univ →
      FractionalManifoldRegularity.Regular (E := WithLp 2 (E × ToralCatMap.Model)) (F := ℝ)
        (h.r - 1) (ζ * (fun z => w z.1)) := fun ζ hζ _ => by
    have smooth := FractionalManifoldRegularity.regular_of_smooth hζ
      (by linarith [h.regularity_gt_one] : (0 : ℝ) ≤ h.r - 1)
    convert smooth.mul productWeight using 1
    funext z
    simp only [Pi.mul_apply, mul_one]
  exact NativeStabilizedLocalLeading.stability_and_retention h a
    (proved_fractionalProductCalculus h.r) (proved_hilbertScalarProductRegularity (h.r - 1)) P L w
    hw hw0 agree (V ×ˢ univ) (h.basic.open_neighborhood.prod isOpen_univ)
    (Set.prod_mono h.basic.subset_neighborhood subset_rfl) subset_rfl smoothProduct φ weight_exp

end ConditionedStochasticStabilityHyperbolic.Paper.NativeLocalTheorem
