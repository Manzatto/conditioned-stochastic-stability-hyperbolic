module
public import ConditionedStochasticStabilityHyperbolic.Paper.AuxiliaryAnosov
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductSplitting
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductRegularNoise
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseRegularityChange

/-! Literal product HL and noise, with no original endpoint dimension
restriction. The actual product tangent identification and ordinary fractional
coordinate calculus precede the stochastic analytic construction. -/
@[expose] public noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualSaddleStabilization
open LeanShared HyperbolicBasicSet RegularNoise
variable {E F X Y ι κ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [MeasurableSpace Y] [BorelSpace Y]
  [Fintype ι] [Fintype κ]
  {T : X ≃ₜ X} {g : X → ℝ} {Λ V : Set X}
  (h : HL (E := E) T g Λ V)
  (a : AuxiliaryAnosov (F := F) (Y := Y) (ι := κ) h.r)

local instance actualSaddleOrdinaryCharts : ChartedSpace (E × F) (X × Y) := productCharts
local instance actualSaddleOrdinaryManifold : IsManifold (𝓘(ℝ, E × F)) ∞ (X × Y) := productManifold

local instance actualSaddleProductCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance actualSaddleProductManifold : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold

variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]
  (productCalculus : FractionalProductCalculus (E := E) (F := F) (X := X) (Y := Y) h.r)
  (linearCalculus : LinearFractionalCalculus (T := T.prodCongr a.map)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F)) h.r)
  (weightCalculus : HilbertScalarProductRegularity (E := E) (F := F)
    (X := X) (Y := Y) (h.r - 1))
  (tangent : HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr a.map) (Λ ×ˢ univ))
  (dense : ∃ z ∈ Λ ×ˢ univ,
    Λ ×ˢ univ ⊆ closure (range (orbit (T.prodCongr a.map) z)))

def outer : HL (E := WithLp 2 (E × F)) (T.prodCongr a.map)
    (fun z : X × Y => g z.1 * (1 : ℝ)) (Λ ×ˢ univ) (V ×ˢ univ) :=
  h.hilbertProduct a.hl productCalculus linearCalculus a.regularity weightCalculus tangent dense

def auxiliaryNoise : Maps (E := F) (ι := κ) a.map a.hl.r :=
  a.noise.changeRegularity a.regularity.symm

def originalForAuxiliary (P : Maps (E := E) (ι := ι) T h.r) :
    Maps (E := E) (ι := ι) T a.hl.r := P.changeRegularity a.regularity.symm

def noise (P : Maps (E := E) (ι := ι) T h.r) :
    Maps (E := WithLp 2 (E × F)) (ι := ι ⊕ κ) (T.prodCongr a.map) h.r :=
  productHilbertMaps P a.noise h.map_regular (by simpa only [a.regularity] using a.hl.map_regular)
    productCalculus linearCalculus

omit [FiniteDimensional ℝ E] [BorelSpace Y]
  [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)] in
theorem noise_family (P : Maps (E := E) (ι := ι) T h.r)
    (ε : ℝ≥0) (control : Control (ι := ι ⊕ κ)) (z : X × Y) :
    (noise h a productCalculus linearCalculus P).family ε control z =
      independentFamily (originalForAuxiliary h a P) (auxiliaryNoise h a) ε control z := by
  simp only [noise, productHilbertMaps_family, independentFamily,
    originalForAuxiliary, auxiliaryNoise, Maps.changeRegularity_family]

variable (splitting : ProductSplittingIdentification h.basic.hyperbolic a.hl.basic.hyperbolic tangent)

omit [BorelSpace Y] in
include splitting in
theorem stable_positive : ∀ z ∈ Λ ×ˢ (univ : Set Y),
    0 < Module.finrank ℝ (tangent.stable z) :=
  splitting.stable_positive h.basic.hyperbolic a.hl.basic.hyperbolic tangent
    (fun y _ => a.stable_positive y)

omit [BorelSpace Y] in
include splitting in
theorem unstable_positive : ∀ z ∈ Λ ×ˢ (univ : Set Y),
    0 < Module.finrank ℝ (tangent.unstable z) :=
  splitting.unstable_positive h.basic.hyperbolic a.hl.basic.hyperbolic tangent
    (fun y _ => a.unstable_positive y)

end ConditionedStochasticStabilityHyperbolic.Paper.ActualSaddleStabilization
