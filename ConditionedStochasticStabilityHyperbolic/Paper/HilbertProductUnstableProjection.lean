module

public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductUnstableFiber
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
local instance hilbertProductUnstableProjectionLocal1 : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hilbertProductUnstableProjectionLocal2 : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]

variable {T : X ≃ₜ X} {S : Y ≃ₜ Y} {K : Set X} {L : Set Y}
  (a : HyperbolicData (E := E) T K) (b : HyperbolicData (E := F) S L)
  (c : HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr S) (K ×ˢ L))



namespace ProductSplittingIdentification

theorem unstableFiber_symm_fst (p : ProductSplittingIdentification a b c)
    (z : X × Y) (hz : z ∈ K ×ˢ L) (w : c.unstable z) :
    ((p.unstableFiber a b c z hz).symm w).fst.val =
      mfderiv (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,E)) Prod.fst z w.val := by
  have same := congrArg (fun v : c.unstable z => ((p.fiber z).symm v.val).1)
    ((p.unstableFiber a b c z hz).apply_symm_apply w)
  rw [p.unstableFiber_apply,ContinuousLinearEquiv.symm_apply_apply,p.first_projection] at same
  exact same

theorem unstableFiber_symm_snd (p : ProductSplittingIdentification a b c)
    (z : X × Y) (hz : z ∈ K ×ˢ L) (w : c.unstable z) :
    ((p.unstableFiber a b c z hz).symm w).snd.val =
      mfderiv (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,F)) Prod.snd z w.val := by
  have same := congrArg (fun v : c.unstable z => ((p.fiber z).symm v.val).2)
    ((p.unstableFiber a b c z hz).apply_symm_apply w)
  rw [p.unstableFiber_apply,ContinuousLinearEquiv.symm_apply_apply,p.second_projection] at same
  exact same

end ProductSplittingIdentification
end ConditionedStochasticStabilityHyperbolic.Paper
