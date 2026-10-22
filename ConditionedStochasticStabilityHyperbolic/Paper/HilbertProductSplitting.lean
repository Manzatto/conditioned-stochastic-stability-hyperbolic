module
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductHL
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Span.Basic

/-! Saddle dimensions of the actual stabilized tangent splitting. The
ordinary product splitting identification is stated through the genuine
projection differentials. Both product dimensions are derived from the
auxiliary saddle, without any original-factor saddle assumption. -/
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
local instance hilbertProductSplittingLocal1 : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hilbertProductSplittingLocal2 : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]

variable {T : X ≃ₜ X} {S : Y ≃ₜ Y} {K : Set X} {L : Set Y}
  (a : HyperbolicData (E := E) T K) (b : HyperbolicData (E := F) S L)
  (c : HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr S) (K ×ˢ L))

/-- The canonical product tangent identification, with its literal
projection derivatives and direct-sum stable/unstable restrictions. -/
structure ProductSplittingIdentification where
  fiber : ∀ z : X × Y,
    (TangentSpace (𝓘(ℝ, E)) z.1 × TangentSpace (𝓘(ℝ, F)) z.2) ≃L[ℝ]
      TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z
  first_projection : ∀ z v, ((fiber z).symm v).1 =
    mfderiv (𝓘(ℝ, WithLp 2 (E × F))) (𝓘(ℝ, E)) Prod.fst z v
  second_projection : ∀ z v, ((fiber z).symm v).2 =
    mfderiv (𝓘(ℝ, WithLp 2 (E × F))) (𝓘(ℝ, F)) Prod.snd z v
  stable : ∀ z ∈ K ×ˢ L, c.stable z =
    ((a.stable z.1).prod (b.stable z.2)).map (fiber z).toLinearMap
  unstable : ∀ z ∈ K ×ˢ L, c.unstable z =
    ((a.unstable z.1).prod (b.unstable z.2)).map (fiber z).toLinearMap

namespace ProductSplittingIdentification
variable (p : ProductSplittingIdentification a b c)
include p

theorem stable_finrank (z : X × Y) (hz : z ∈ K ×ˢ L) :
    Module.finrank ℝ (c.stable z) =
      Module.finrank ℝ (a.stable z.1) + Module.finrank ℝ (b.stable z.2) := by
  rw [p.stable z hz, LinearEquiv.finrank_map_eq (p.fiber z).toLinearEquiv,
    (Submodule.prodEquiv (a.stable z.1) (b.stable z.2)).finrank_eq,
    Module.finrank_prod]

theorem unstable_finrank (z : X × Y) (hz : z ∈ K ×ˢ L) :
    Module.finrank ℝ (c.unstable z) =
      Module.finrank ℝ (a.unstable z.1) + Module.finrank ℝ (b.unstable z.2) := by
  rw [p.unstable z hz, LinearEquiv.finrank_map_eq (p.fiber z).toLinearEquiv,
    (Submodule.prodEquiv (a.unstable z.1) (b.unstable z.2)).finrank_eq,
    Module.finrank_prod]

theorem stable_positive (hb : ∀ y ∈ L, 0 < Module.finrank ℝ (b.stable y)) :
    ∀ z ∈ K ×ˢ L, 0 < Module.finrank ℝ (c.stable z) := by
  intro z hz
  rw [p.stable_finrank a b c z hz]
  exact Nat.add_pos_right _ (hb z.2 hz.2)

theorem unstable_positive (hb : ∀ y ∈ L, 0 < Module.finrank ℝ (b.unstable y)) :
    ∀ z ∈ K ×ˢ L, 0 < Module.finrank ℝ (c.unstable z) := by
  intro z hz
  rw [p.unstable_finrank a b c z hz]
  exact Nat.add_pos_right _ (hb z.2 hz.2)

end ProductSplittingIdentification
end ConditionedStochasticStabilityHyperbolic.Paper
