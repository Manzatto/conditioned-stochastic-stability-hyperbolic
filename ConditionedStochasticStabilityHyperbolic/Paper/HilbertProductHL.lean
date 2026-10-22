module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProductHL
public import ConditionedStochasticStabilityHyperbolic.Paper.LinearRechartedNoise

/-! The literal stabilized HL datum in genuine Hilbert product coordinates.
The remaining classical geometry is the actual product tangent splitting
and Birkhoff dense orbit; no stochastic or spectral conclusion is supplied. -/

@[expose] public noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet RegularNoise

variable {E F X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  {T : X ≃ₜ X} {S : Y ≃ₜ Y} {g : X → ℝ} {h : Y → ℝ}
  {Λ V : Set X} {Γ W : Set Y}
  (a : HL (E := E) T g Λ V) (b : HL (E := F) S h Γ W)

local instance hilbertProductHLLocal1 : ChartedSpace (E × F) (X × Y) := RegularNoise.productCharts
local instance hilbertProductHLLocal2 : IsManifold (𝓘(ℝ, E × F)) ∞ (X × Y) := RegularNoise.productManifold

variable
  (productCalculus : FractionalProductCalculus (E := E) (F := F) (X := X) (Y := Y) a.r)
  (linearCalculus : LinearFractionalCalculus (T := T.prodCongr S)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F)) a.r)

local instance hilbertProductHLLocal3 : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hilbertProductHLLocal4 : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold

variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]

/-- Ordinary C^q scalar product calculus in the constructed Hilbert charts. -/
def HilbertScalarProductRegularity (q : ℝ) : Prop :=
  ∀ (f : X → ℝ) (k : Y → ℝ),
    FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q f →
    FractionalManifoldRegularity.Regular (E := F) (F := ℝ) q k →
    FractionalManifoldRegularity.Regular (E := WithLp 2 (E × F)) (F := ℝ) q
      (fun z : X × Y => f z.1 * k z.2)

/-- Genuine Hilbert-model HL, including literal weight and core. -/
def HL.hilbertProduct (hr : b.r = a.r)
    (weightCalculus : HilbertScalarProductRegularity (E := E) (F := F) (X := X) (Y := Y) (a.r - 1))
    (tangentProduct : HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr S) (Λ ×ˢ Γ))
    (denseOrbit : ∃ z ∈ Λ ×ˢ Γ, Λ ×ˢ Γ ⊆ closure (range (orbit (T.prodCongr S) z))) :
    HL (E := WithLp 2 (E × F)) (T.prodCongr S)
      (fun z : X × Y => g z.1 * h z.2) (Λ ×ˢ Γ) (V ×ˢ W) where
  r := a.r
  regularity_gt_one := a.regularity_gt_one
  map_regular := linearCalculus.regular _
    (productCalculus.regular T S a.map_regular (by simpa only [hr] using b.map_regular))
  inverse_regular := linearCalculus.regular _
    (productCalculus.regular T.symm S.symm a.inverse_regular
      (by simpa only [hr] using b.inverse_regular))
  basic := {
    hyperbolic := tangentProduct
    nonempty := a.nonempty_core.prod b.nonempty_core
    open_neighborhood := a.basic.open_neighborhood.prod b.basic.open_neighborhood
    subset_neighborhood := Set.prod_mono a.basic.subset_neighborhood b.basic.subset_neighborhood
    isolated := by
      rw [closure_prod_eq, isolatedCore_product, ← a.actual_isolated_core, ← b.actual_isolated_core]
    dense_orbit := denseOrbit }
  weight_regular := weightCalculus g h a.weight_regular (by simpa only [hr] using b.weight_regular)
  weight_nonnegative z := mul_nonneg (a.weight_nonnegative z.1) (b.weight_nonnegative z.2)
  weight_supported := (tsupport_independent_weight g h).trans
    (Set.prod_mono a.weight_supported b.weight_supported)
  weight_positive z hz := mul_pos (a.weight_positive z.1 hz.1) (b.weight_positive z.2 hz.2)
  mixing := a.mixing.product b.mixing

end ConditionedStochasticStabilityHyperbolic.Paper
