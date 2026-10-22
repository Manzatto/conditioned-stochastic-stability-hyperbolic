module

public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductSplitting
public import LeanShared.Geometry.HilbertProductDifferential

/-! The actual product derivative is conjugate to the two genuine factor
derivatives through the canonical projection-based tangent identification. -/
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
local instance hilbertProductDerivativeConjugacyLocal1 : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hilbertProductDerivativeConjugacyLocal2 : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]

variable {T : X ≃ₜ X} {S : Y ≃ₜ Y} {K : Set X} {L : Set Y}
  (a : HyperbolicData (E := E) T K) (b : HyperbolicData (E := F) S L)
  (c : HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr S) (K ×ˢ L))


namespace ProductSplittingIdentification

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem differential_conjugacy (p : ProductSplittingIdentification a b c)
    (forwardT : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (forwardS : MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S)
    (forwardProduct : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F)))
      (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S)) (z : X × Y)
    (v : TangentSpace (𝓘(ℝ,E)) z.1 × TangentSpace (𝓘(ℝ,F)) z.2) :
    mfderiv (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S) z (p.fiber z v) =
      p.fiber (T.prodCongr S z)
        (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T z.1 v.1,
          mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) S z.2 v.2) := by
  have literal : (T.prodCongr S : X × Y → X × Y)=Prod.map (T : X → X) (S : Y → Y) := rfl
  rw [literal]
  apply (p.fiber (Prod.map (T : X → X) (S : Y → Y) z)).symm.injective
  apply Prod.ext
  · rw [ContinuousLinearEquiv.symm_apply_apply,p.first_projection]
    have same := congrArg (fun A => A (p.fiber z v))
      (HilbertProductDifferential.fst_intertwines (T : X → X) (S : Y → Y)
        forwardT forwardProduct z)
    simpa only [ContinuousLinearMap.comp_apply,←p.first_projection,
      ContinuousLinearEquiv.symm_apply_apply] using same
  · rw [ContinuousLinearEquiv.symm_apply_apply,p.second_projection]
    have same := congrArg (fun A => A (p.fiber z v))
      (HilbertProductDifferential.snd_intertwines (T : X → X) (S : Y → Y)
        forwardS forwardProduct z)
    simpa only [ContinuousLinearMap.comp_apply,←p.second_projection,
      ContinuousLinearEquiv.symm_apply_apply] using same

end ProductSplittingIdentification
end ConditionedStochasticStabilityHyperbolic.Paper
