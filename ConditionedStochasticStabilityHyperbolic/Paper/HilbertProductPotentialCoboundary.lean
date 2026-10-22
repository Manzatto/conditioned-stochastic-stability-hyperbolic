module

public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductJacobianCocycle
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductVolumeContinuity

/-! The literal product thermodynamic potential differs from the sum of the
factor potentials by a proved continuous core coboundary. Arbitrary product
Riemannian metrics are retained. -/
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
local instance hilbertProductPotentialCoboundaryLocal1 : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hilbertProductPotentialCoboundaryLocal2 : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]
variable [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace (𝓘(ℝ,F)) : Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)]

variable {T : X ≃ₜ X} {S : Y ≃ₜ Y} {K : Set X} {L : Set Y}
  (a : HyperbolicData (E := E) T K) (b : HyperbolicData (E := F) S L)
  (c : HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr S) (K ×ˢ L))





namespace ProductSplittingIdentification

omit [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace (𝓘(ℝ,F)) : Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)] in
theorem unstableVolume_positive (p : ProductSplittingIdentification a b c)
    (z : X × Y) (hz : z ∈ K ×ˢ L) : 0 < p.unstableVolume a b c z := by
  classical
  rw [unstableVolume,dite_eq_left hz]
  apply lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm ?_)
  intro zero
  exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp zero)
    (LinearMap.ker_eq_bot.mpr (p.unstableFiber a b c z hz).injective)

theorem continuousOn_log_unstableVolume (p : ProductSplittingIdentification a b c) :
    ContinuousOn (fun z => Real.log (p.unstableVolume a b c z)) (K ×ˢ L) :=
  (p.continuousOn_unstableVolume a b c).log
    (fun z hz => ne_of_gt (p.unstableVolume_positive a b c z hz))

omit [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ,E)) : X → Type _)]
  [IsContinuousRiemannianBundle F (TangentSpace (𝓘(ℝ,F)) : Y → Type _)]
  [IsContinuousRiemannianBundle (WithLp 2 (E × F))
    (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)] in
theorem potential_coboundary (p : ProductSplittingIdentification a b c)
    (forwardT : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverseT : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (forwardS : MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S)
    (inverseS : MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S.symm)
    (forwardProduct : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F)))
      (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S))
    (inverseProduct : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F)))
      (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S).symm)
    (g : X → ℝ) (h : Y → ℝ) (gpositive : ∀ x ∈ K, 0 < g x) (hpositive : ∀ y ∈ L, 0 < h y) :
    EqOn (c.potential (fun z => g z.1*h z.2))
      (fun z => a.potential g z.1+b.potential h z.2+
        Real.log (p.unstableVolume a b c z)-Real.log (p.unstableVolume a b c (T.prodCongr S z)))
      (K ×ˢ L) := by
  classical
  intro z hz
  obtain ⟨ht,identity⟩ := p.logarithmic_unstableJacobian a b c
    forwardT inverseT forwardS inverseS forwardProduct inverseProduct z hz
  simp only [unstableVolume,dite_eq_left hz,dite_eq_left ht]
  simp only [HyperbolicData.potential]
  rw [Real.log_mul (ne_of_gt (gpositive z.1 hz.1)) (ne_of_gt (hpositive z.2 hz.2))]
  linarith

end ProductSplittingIdentification
end ConditionedStochasticStabilityHyperbolic.Paper
