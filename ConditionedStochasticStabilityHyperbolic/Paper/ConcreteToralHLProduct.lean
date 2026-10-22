module
public import ConditionedStochasticStabilityHyperbolic.Paper.ToralCatMapHL
public import ConditionedStochasticStabilityHyperbolic.Paper.ProductHL
public import LeanShared.Geometry.FractionalCartesianMapRegularity
public import LeanShared.Geometry.FractionalLinearRechartRegularity
public import LeanShared.Geometry.FractionalHilbertProjection
public import LeanShared.Geometry.IntrinsicSmoothRiemannianMetric
public import LeanShared.Dynamics.HyperbolicHilbertProduct
public import LeanShared.Dynamics.MixingDenseOrbit

/-! A literal original-times-concrete-cat HL system in an internally
constructed smooth metric. No product metric, tangent hyperbolicity,
product fractional calculus or product dense orbit is an input. -/
@[expose] public noncomputable section
open Set Bundle IsManifold Function
open scoped Manifold ContDiff Bundle Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.ConcreteToralHLProduct
open LeanShared HyperbolicBasicSet
abbrev Auxiliary := LeanShared.ToralCatMap.Torus
abbrev AuxiliaryModel := LeanShared.ToralCatMap.HilbertModel
abbrev Model (E : Type*) := WithLp 2 (E × AuxiliaryModel)
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace X] [CompactSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (TangentSpace (𝓘(ℝ, E)) (M := X))]
  [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ, E)) (M := X))]
  {T : X ≃ₜ X} {g : X → ℝ} {Λ V : Set X}

local instance ordinaryCharts : ChartedSpace (E × AuxiliaryModel) (X × Auxiliary) :=
  prodChartedSpace E X AuxiliaryModel Auxiliary
local instance productCharts : ChartedSpace (Model E) (X × Auxiliary) :=
  LinearRechartedManifold.productCharts
local instance productManifold : IsManifold (𝓘(ℝ, Model E)) ∞ (X × Auxiliary) :=
  LinearRechartedManifold.product_manifold

/-- The product metric is actually constructed, rather than supplied. -/
def metric : ContMDiffRiemannianMetric (𝓘(ℝ, Model E)) ∞ (Model E)
    (TangentSpace (𝓘(ℝ, Model E)) (M := X × Auxiliary)) :=
  IntrinsicSmoothRiemannianMetric.smoothMetric

@[instance_reducible] def bundle : RiemannianBundle (TangentSpace (𝓘(ℝ, Model E)) (M := X × Auxiliary)) :=
  ⟨(metric (E := E) (X := X)).toRiemannianMetric⟩

local instance productBundle : RiemannianBundle (TangentSpace (𝓘(ℝ, Model E)) (M := X × Auxiliary)) := bundle
local instance productContinuous : IsContinuousRiemannianBundle (Model E)
    (TangentSpace (𝓘(ℝ, Model E)) (M := X × Auxiliary)) :=
  SmoothMetricBundleClasses.continuous (metric (E := E) (X := X))
local instance productSmooth : IsContMDiffRiemannianBundle (𝓘(ℝ, Model E)) ∞ (Model E)
    (TangentSpace (𝓘(ℝ, Model E)) (M := X × Auxiliary)) :=
  SmoothMetricBundleClasses.smooth (metric (E := E) (X := X))

omit [FiniteDimensional ℝ E] [CompactSpace X]
  [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ, E)) (M := X))] in
theorem mapRegular (h : HL (E := E) T g Λ V) :
    FractionalManifoldRegularity.Regular (E := Model E) (F := Model E) h.r
      (T.prodCongr LeanShared.ToralCatMap.homeomorph) :=
  (h.map_regular.prod_map (ToralCatMap.hl h.r h.regularity_gt_one).map_regular).linearRechart
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := AuxiliaryModel))

omit [FiniteDimensional ℝ E] [CompactSpace X]
  [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ, E)) (M := X))] in
theorem inverseRegular (h : HL (E := E) T g Λ V) :
    FractionalManifoldRegularity.Regular (E := Model E) (F := Model E) h.r
      (T.prodCongr LeanShared.ToralCatMap.homeomorph).symm :=
  (h.inverse_regular.prod_map (ToralCatMap.hl h.r h.regularity_gt_one).inverse_regular).linearRechart
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := AuxiliaryModel))

def hyperbolic (h : HL (E := E) T g Λ V) :
    HyperbolicData (E := Model E) (T.prodCongr LeanShared.ToralCatMap.homeomorph)
      (Λ ×ˢ (univ : Set Auxiliary)) :=
  HilbertProduct.of_factors h.basic.hyperbolic (ToralCatMap.hl h.r h.regularity_gt_one).basic.hyperbolic
    (h.map_regular.mdifferentiable h.regularity_gt_one.le)
    (h.inverse_regular.mdifferentiable h.regularity_gt_one.le)
    ((ToralCatMap.hl h.r h.regularity_gt_one).map_regular.mdifferentiable h.regularity_gt_one.le)
    ((ToralCatMap.hl h.r h.regularity_gt_one).inverse_regular.mdifferentiable h.regularity_gt_one.le)

/-- Genuine product HL, preserving the literal original departure weight. -/
def hl (h : HL (E := E) T g Λ V) :
    HL (E := Model E) (T.prodCongr LeanShared.ToralCatMap.homeomorph)
      (fun z : X × Auxiliary => g z.1) (Λ ×ˢ univ) (V ×ˢ univ) where
  r := h.r
  regularity_gt_one := h.regularity_gt_one
  map_regular := mapRegular h
  inverse_regular := inverseRegular h
  basic := {
    hyperbolic := hyperbolic h
    nonempty := h.nonempty_core.prod (ToralCatMap.hl h.r h.regularity_gt_one).nonempty_core
    open_neighborhood := h.basic.open_neighborhood.prod isOpen_univ
    subset_neighborhood := Set.prod_mono h.basic.subset_neighborhood (subset_refl _)
    isolated := by
      rw [closure_prod_eq, isolatedCore_product, ← h.actual_isolated_core,
        ← (ToralCatMap.hl h.r h.regularity_gt_one).actual_isolated_core]
    dense_orbit := h.mixing.exists_product_dense_orbit
      (ToralCatMap.hl h.r h.regularity_gt_one).mixing h.compact_core
      (ToralCatMap.hl h.r h.regularity_gt_one).compact_core h.nonempty_core
      (ToralCatMap.hl h.r h.regularity_gt_one).nonempty_core h.basic.hyperbolic.invariant
      (ToralCatMap.hl h.r h.regularity_gt_one).basic.hyperbolic.invariant }
  weight_regular := h.weight_regular.hilbert_fst
  weight_nonnegative z := h.weight_nonnegative z.1
  weight_supported := by
    simpa only [mul_one] using (tsupport_independent_weight g (fun _ : Auxiliary => (1 : ℝ))).trans
      (Set.prod_mono h.weight_supported (subset_univ _))
  weight_positive z hz := h.weight_positive z.1 hz.1
  mixing := h.mixing.product (ToralCatMap.hl h.r h.regularity_gt_one).mixing

/-- No saddle assumption on the original factor is needed. -/
theorem stable_positive (h : HL (E := E) T g Λ V) (z : X × Auxiliary) :
    0 < Module.finrank ℝ ((hl h).basic.hyperbolic.stable z) := by
  change 0 < Module.finrank ℝ (HilbertProduct.stable h.basic.hyperbolic
    (ToralCatMap.hl h.r h.regularity_gt_one).basic.hyperbolic z)
  rw [HilbertProduct.stable, LinearEquiv.finrank_map_eq (HilbertProductDifferential.tangentEquiv z).toLinearEquiv,
    (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]
  exact Nat.add_pos_right _ (ToralCatMap.hl_stable_positive h.r h.regularity_gt_one z.2)

theorem unstable_positive (h : HL (E := E) T g Λ V) (z : X × Auxiliary) :
    0 < Module.finrank ℝ ((hl h).basic.hyperbolic.unstable z) := by
  change 0 < Module.finrank ℝ (HilbertProduct.unstable h.basic.hyperbolic
    (ToralCatMap.hl h.r h.regularity_gt_one).basic.hyperbolic z)
  rw [HilbertProduct.unstable, LinearEquiv.finrank_map_eq (HilbertProductDifferential.tangentEquiv z).toLinearEquiv,
    (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]
  exact Nat.add_pos_right _ (ToralCatMap.hl_unstable_positive h.r h.regularity_gt_one z.2)

end ConditionedStochasticStabilityHyperbolic.Paper.ConcreteToralHLProduct
