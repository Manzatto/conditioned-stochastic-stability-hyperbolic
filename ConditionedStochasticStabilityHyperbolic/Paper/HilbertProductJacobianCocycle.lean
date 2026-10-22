module

public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductDerivativeConjugacy
public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductUnstableFiber
public import LeanShared.Dynamics.HyperbolicUnstableJacobian
import Mathlib.Tactic.Linarith

/-! Exact actual unstable-Jacobian cocycle under arbitrary product metrics.
The metric correction is the genuine unstable-fiber volume change; no
isometric product splitting or Jacobian multiplicativity is assumed. -/
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
local instance hilbertProductJacobianCocycleLocal1 : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hilbertProductJacobianCocycleLocal2 : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]

variable {T : X ≃ₜ X} {S : Y ≃ₜ Y} {K : Set X} {L : Set Y}
  (a : HyperbolicData (E := E) T K) (b : HyperbolicData (E := F) S L)
  (c : HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr S) (K ×ˢ L))




namespace ProductSplittingIdentification

theorem logarithmic_unstableJacobian (p : ProductSplittingIdentification a b c)
    (forwardT : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverseT : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (forwardS : MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S)
    (inverseS : MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S.symm)
    (forwardProduct : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F)))
      (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S))
    (inverseProduct : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F)))
      (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S).symm)
    (z : X × Y) (hz : z ∈ K ×ˢ L) :
    ∃ ht : T.prodCongr S z ∈ K ×ˢ L,
      Real.log (c.unstableJacobian z) =
        Real.log (a.unstableJacobian z.1)+Real.log (b.unstableJacobian z.2)+
          Real.log (p.unstableFiber a b c (T.prodCongr S z) ht).toLinearMap.normDet -
            Real.log (p.unstableFiber a b c z hz).toLinearMap.normDet := by
  have ht : T.prodCongr S z ∈ K ×ˢ L := by
    constructor
    · rw [←a.invariant]
      exact mem_image_of_mem T hz.1
    · rw [←b.invariant]
      exact mem_image_of_mem S hz.2
  refine ⟨ht,?_⟩
  let AT := a.unstableDifferential forwardT inverseT z.1 hz.1
  let AS := b.unstableDifferential forwardS inverseS z.2 hz.2
  let AP := c.unstableDifferential forwardProduct inverseProduct z hz
  let A := (L2ProductNormDet.productEquiv AT.toLinearEquiv AS.toLinearEquiv).toContinuousLinearEquiv
  let H := p.unstableFiber a b c z hz
  let Ht : WithLp 2 (a.unstable (T z.1) × b.unstable (S z.2)) ≃L[ℝ]
      c.unstable (T.prodCongr S z) := p.unstableFiber a b c (T.prodCongr S z) ht
  have conjugacy : AP.toLinearMap.comp H.toLinearMap=Ht.toLinearMap.comp A.toLinearMap := by
    ext v
    change mfderiv (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,WithLp 2 (E × F))) (T.prodCongr S) z
      (p.fiber z (v.fst.val,v.snd.val)) =
        p.fiber (T.prodCongr S z)
          (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T z.1 v.fst.val,
            mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) S z.2 v.snd.val)
    exact p.differential_conjugacy a b c forwardT forwardS forwardProduct z _
  have leftDet := LinearMap.normDet_comp_of_finrank_eq H.toLinearMap AP.toLinearMap H.toLinearEquiv.finrank_eq
  have rightDet := LinearMap.normDet_comp_of_finrank_eq A.toLinearMap Ht.toLinearMap A.toLinearEquiv.finrank_eq
  have determinants := leftDet.symm.trans ((congrArg LinearMap.normDet conjugacy).trans rightDet)
  have factor : A.toLinearMap.normDet=a.unstableJacobian z.1*b.unstableJacobian z.2 := by
    rw [a.unstableJacobian_eq_normDet forwardT inverseT z.1 hz.1,
      b.unstableJacobian_eq_normDet forwardS inverseS z.2 hz.2]
    exact L2ProductNormDet.normDet_product AT.toLinearEquiv AS.toLinearEquiv
  have product : AP.toLinearMap.normDet=c.unstableJacobian z :=
    (c.unstableJacobian_eq_normDet forwardProduct inverseProduct z hz).symm
  rw [factor,product] at determinants
  have hn : H.toLinearMap.normDet ≠ 0 := by
    intro zero
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp zero) (LinearMap.ker_eq_bot.mpr H.injective)
  have htn : Ht.toLinearMap.normDet ≠ 0 := by
    intro zero
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp zero) (LinearMap.ker_eq_bot.mpr Ht.injective)
  have an := ne_of_gt (a.unstableJacobian_positive forwardT inverseT z.1 hz.1)
  have bn := ne_of_gt (b.unstableJacobian_positive forwardS inverseS z.2 hz.2)
  have cn := ne_of_gt (c.unstableJacobian_positive forwardProduct inverseProduct z hz)
  have logs := congrArg Real.log determinants
  rw [Real.log_mul cn hn,Real.log_mul htn (mul_ne_zero an bn),Real.log_mul an bn] at logs
  change Real.log (c.unstableJacobian z)=Real.log (a.unstableJacobian z.1)+
    Real.log (b.unstableJacobian z.2)+Real.log Ht.toLinearMap.normDet-Real.log H.toLinearMap.normDet
  linarith

end ProductSplittingIdentification
end ConditionedStochasticStabilityHyperbolic.Paper
