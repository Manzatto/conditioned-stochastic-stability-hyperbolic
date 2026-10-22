module
public import LeanShared.Geometry.SmoothFractionalRegularity
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualSaddleStabilization
public import ConditionedStochasticStabilityHyperbolic.Paper.AdaptedLocalWeightSupportedProduct

/-! The auxiliary and product collars/cutoffs are constructed before their
ordinary analytic sources are instantiated. No trapping, retained weight
agreement or product process identity is supplied by an analytic source. -/
@[expose] public noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.ConstructedSaddleLocalSetup
open LeanShared HyperbolicBasicSet RegularNoise
variable {E F X Y ι κ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [CompactSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [CompactSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [MeasurableSpace Y] [BorelSpace Y] [Fintype ι] [Fintype κ]
  {T : X ≃ₜ X} {g : X → ℝ} {Λ V : Set X}
  (h : HL (E := E) T g Λ V)
  (a : AuxiliaryAnosov (F := F) (Y := Y) (ι := κ) h.r)

local instance constructedSaddleOrdinaryCharts : ChartedSpace (E × F) (X × Y) := productCharts
local instance constructedSaddleOrdinaryManifold : IsManifold (𝓘(ℝ, E × F)) ∞ (X × Y) := productManifold
local instance constructedSaddleProductCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance constructedSaddleProductManifold : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
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

local notation "outer" => ActualSaddleStabilization.outer h a productCalculus linearCalculus weightCalculus tangent dense

/-- Smooth-to-fractional regularity for the constant auxiliary departure
weight is derived from its literal smoothness. -/
def auxiliarySetup :
    AdaptedLocalWeightSetup.Data a.hl (fun _ => 1) univ :=
  AdaptedLocalWeightSetup.of_supported_product a.hl (fun _ => 1) univ
    isOpen_univ subset_rfl subset_rfl continuous_const (fun _ _ => rfl)
    (fun ζ hs _ => by
      have identity : ζ * (fun _ => (1 : ℝ)) = ζ := by
        funext y
        exact mul_one (ζ y)
      exact identity.symm ▸ FractionalManifoldRegularity.regular_of_smooth hs
        (sub_nonneg.mpr a.hl.regularity_gt_one.le))

variable (w : X → ℝ) (hw : Continuous w) (agree : EqOn w g Λ)
  (W : Set (X × Y)) (hW : IsOpen W) (coreW : Λ ×ˢ (univ : Set Y) ⊆ W)
  (within : W ⊆ V ×ˢ univ)
  (smoothProduct : ∀ ζ : X × Y → ℝ,
    ContMDiff (𝓘(ℝ, WithLp 2 (E × F))) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
    FractionalManifoldRegularity.Regular (E := WithLp 2 (E × F)) (F := ℝ)
      (h.r - 1) (ζ * (fun z => w z.1)))

def productSetup : AdaptedLocalWeightSetup.Data outer (fun z => w z.1) W :=
  AdaptedLocalWeightSetup.of_supported_product outer (fun z => w z.1) W hW coreW within
    (hw.comp continuous_fst) (fun z hz => by simpa only [mul_one] using agree hz.1)
    smoothProduct

local notation "setup" => productSetup h a productCalculus linearCalculus weightCalculus tangent dense w hw agree W hW coreW within smoothProduct

def productNoise (P : Maps (E := E) (ι := ι) T h.r) :
    Maps (E := WithLp 2 (E × F)) (ι := ι ⊕ κ) (T.prodCongr a.map) (setup).fresh.r :=
  (ActualSaddleStabilization.noise h a productCalculus linearCalculus P).changeRegularity
    ((show (outer).r = h.r from rfl).symm.trans (setup).regularity_eq.symm)

omit [BorelSpace Y] in
theorem productNoise_family (P : Maps (E := E) (ι := ι) T h.r)
    (ε : ℝ≥0) (control : Control (ι := ι ⊕ κ)) (z : X × Y) :
    (productNoise h a productCalculus linearCalculus weightCalculus tangent dense
      w hw agree W hW coreW within smoothProduct P).family ε control z =
    independentFamily (ActualSaddleStabilization.originalForAuxiliary h a P)
      (ActualSaddleStabilization.auxiliaryNoise h a) ε control z := by
  rw [productNoise, Maps.changeRegularity_family, ActualSaddleStabilization.noise_family]

end ConditionedStochasticStabilityHyperbolic.Paper.ConstructedSaddleLocalSetup
