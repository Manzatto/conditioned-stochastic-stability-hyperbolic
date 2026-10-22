module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProductRegularNoiseConstructor
public import LeanShared.Dynamics.ProductIsolationMixing

/-! Literal HL for a Cartesian product. The classical hyperbolic tangent
product and Birkhoff dense-orbit facts are kept separate from the proved
mixing, isolation, support, sign and exact regularity deductions. -/

@[expose] public noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet RegularNoise

variable {E F X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]

local instance productHLLocal1 : ChartedSpace (E × F) (X × Y) := productCharts
local instance productHLLocal2 : IsManifold (𝓘(ℝ, E × F)) ∞ (X × Y) := productManifold

variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, E × F)) z)]

/-- Ordinary fractional multiplication after the two smooth Cartesian
projections. This is a deterministic calculus source at the stated order. -/
def ScalarProductRegularity (q : ℝ) : Prop :=
  ∀ (g : X → ℝ) (h : Y → ℝ),
    FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q g →
    FractionalManifoldRegularity.Regular (E := F) (F := ℝ) q h →
    FractionalManifoldRegularity.Regular (E := E × F) (F := ℝ) q (fun z : X × Y => g z.1 * h z.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, E × F)) z)] in
/-- The product weight is supported in the product collar, including the
boundary of both ordinary supports. -/
theorem tsupport_independent_weight (g : X → ℝ) (h : Y → ℝ) :
    tsupport (fun z : X × Y => g z.1 * h z.2) ⊆ tsupport g ×ˢ tsupport h := by
  change closure (Function.support (fun z : X × Y => g z.1 * h z.2)) ⊆
    closure (Function.support g) ×ˢ closure (Function.support h)
  rw [← closure_prod_eq]
  apply closure_mono
  intro z hz
  exact mul_ne_zero_iff.mp hz

/-- The product HL datum contains the actual product map, core, collar and
weight. No saddle assumption is inserted into either input HL datum.
The two outstanding ordinary dynamics parameters are precisely the tangent
hyperbolic product theorem and dense-orbit/Birkhoff theorem, not a noisy gap. -/
def HL.product {T : X ≃ₜ X} {S : Y ≃ₜ Y} {g : X → ℝ} {h : Y → ℝ}
    {Λ V : Set X} {Γ W : Set Y}
    (a : HL (E := E) T g Λ V) (b : HL (E := F) S h Γ W) (hr : b.r = a.r)
    (calculus : FractionalProductCalculus (E := E) (F := F) (X := X) (Y := Y) a.r)
    (weightCalculus : ScalarProductRegularity (E := E) (F := F) (X := X) (Y := Y) (a.r - 1))
    (tangentProduct : HyperbolicData (E := E × F) (T.prodCongr S) (Λ ×ˢ Γ))
    (denseOrbit : ∃ z ∈ Λ ×ˢ Γ, Λ ×ˢ Γ ⊆ closure (range (orbit (T.prodCongr S) z))) :
    HL (E := E × F) (T.prodCongr S) (fun z : X × Y => g z.1 * h z.2) (Λ ×ˢ Γ) (V ×ˢ W) where
  r := a.r
  regularity_gt_one := a.regularity_gt_one
  map_regular := calculus.regular T S a.map_regular (by simpa only [hr] using b.map_regular)
  inverse_regular := calculus.regular T.symm S.symm a.inverse_regular
    (by simpa only [hr] using b.inverse_regular)
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
