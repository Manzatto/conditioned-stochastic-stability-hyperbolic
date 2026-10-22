module

public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductSplitting
public import LeanShared.Geometry.L2ProductNormDet
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual unstable product fibers are identified with the Hilbert product
of the two factor unstable spaces. This is a genuine linear equivalence,
not an unjustified isometry for an arbitrary product Riemannian metric. -/
public noncomputable section
open Set Function Bundle
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet
variable {E F X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
local instance hilbertProductUnstableFiberLocal1 : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hilbertProductUnstableFiberLocal2 : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]

variable {T : X ≃ₜ X} {S : Y ≃ₜ Y} {K : Set X} {L : Set Y}
  (a : HyperbolicData (E := E) T K) (b : HyperbolicData (E := F) S L)
  (c : HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr S) (K ×ˢ L))



namespace ProductSplittingIdentification

@[expose] def unstableFiber (p : ProductSplittingIdentification a b c)
    (z : X × Y) (hz : z ∈ K ×ˢ L) :
    WithLp 2 (a.unstable z.1 × b.unstable z.2) ≃L[ℝ] c.unstable z :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (a.unstable z.1) (b.unstable z.2)).trans
    (((Submodule.prodEquiv (a.unstable z.1) (b.unstable z.2)).symm.toContinuousLinearEquiv).trans
      ((p.fiber z).ofSubmodules _ _ (p.unstable z hz).symm))

theorem unstableFiber_apply (p : ProductSplittingIdentification a b c)
    (z : X × Y) (hz : z ∈ K ×ˢ L) (v : WithLp 2 (a.unstable z.1 × b.unstable z.2)) :
    (p.unstableFiber a b c z hz v).val = p.fiber z (v.fst.val,v.snd.val) := rfl

end ProductSplittingIdentification
end ConditionedStochasticStabilityHyperbolic.Paper
