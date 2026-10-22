module

public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductSplitting
public import LeanShared.Geometry.HilbertProductTangentEquiv
public import LeanShared.Dynamics.HyperbolicSemiconjugacySplitting
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
local instance hilbertProductProvedSplittingLocal1 : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hilbertProductProvedSplittingLocal2 : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z : X × Y => TangentSpace (𝓘(ℝ, WithLp 2 (E × F))) z)]

variable {T : X ≃ₜ X} {S : Y ≃ₜ Y} {K : Set X} {L : Set Y}
  (a : HyperbolicData (E := E) T K) (b : HyperbolicData (E := F) S L)
  (c : HyperbolicData (E := WithLp 2 (E × F)) (T.prodCongr S) (K ×ˢ L))



variable
  [IsContinuousRiemannianBundle E (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle F (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [IsContinuousRiemannianBundle (WithLp 2 (E×F))
    (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)]

namespace ProductSplittingIdentification

/-- Every actual product hyperbolic certificate has the canonical factor
splitting. Both inclusions are derived from bounded derivative orbits. -/
def of_actual_product
    (forwardT:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverseT:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (forwardS:MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S)
    (inverseS:MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S.symm)
    (forwardProduct:MDifferentiable (𝓘(ℝ,WithLp 2 (E×F)))
      (𝓘(ℝ,WithLp 2 (E×F))) (T.prodCongr S))
    (inverseProduct:MDifferentiable (𝓘(ℝ,WithLp 2 (E×F)))
      (𝓘(ℝ,WithLp 2 (E×F))) (T.prodCongr S).symm) :
    ProductSplittingIdentification a b c := by
  let fiber := fun z:X×Y=>HilbertProductDifferential.tangentEquiv (E:=E) (F:=F) z
  refine ⟨fiber,HilbertProductDifferential.tangentEquiv_first (E:=E) (F:=F),
    HilbertProductDifferential.tangentEquiv_second (E:=E) (F:=F),?_,?_⟩
  all_goals
    intro z hz
    have stableLe : c.stable z ≤ ((a.stable z.1).prod (b.stable z.2)).map (fiber z).toLinearMap := by
      intro v hv
      refine ⟨(fiber z).symm v,?_,(fiber z).apply_symm_apply v⟩
      constructor
      · rw [HilbertProductDifferential.tangentEquiv_first]
        exact c.stable_map_semiconjugacy a forwardProduct forwardT inverseT Prod.fst
          (HilbertProductDifferential.smooth_fst.of_le (by norm_num))
          (fun _ hy=>hy.1) (fun _=>rfl) z hz v hv
      · rw [HilbertProductDifferential.tangentEquiv_second]
        exact c.stable_map_semiconjugacy b forwardProduct forwardS inverseS Prod.snd
          (HilbertProductDifferential.smooth_snd.of_le (by norm_num))
          (fun _ hy=>hy.2) (fun _=>rfl) z hz v hv
    have unstableLe : c.unstable z ≤ ((a.unstable z.1).prod (b.unstable z.2)).map (fiber z).toLinearMap := by
      intro v hv
      refine ⟨(fiber z).symm v,?_,(fiber z).apply_symm_apply v⟩
      constructor
      · rw [HilbertProductDifferential.tangentEquiv_first]
        exact c.unstable_map_semiconjugacy a inverseProduct forwardT inverseT Prod.fst
          (HilbertProductDifferential.smooth_fst.of_le (by norm_num))
          (fun _ hy=>hy.1) (fun _=>rfl) z hz v hv
      · rw [HilbertProductDifferential.tangentEquiv_second]
        exact c.unstable_map_semiconjugacy b inverseProduct forwardS inverseS Prod.snd
          (HilbertProductDifferential.smooth_snd.of_le (by norm_num))
          (fun _ hy=>hy.2) (fun _=>rfl) z hz v hv
    have prodDisjoint : Disjoint ((a.stable z.1).prod (b.stable z.2))
        ((a.unstable z.1).prod (b.unstable z.2)) := by
      apply Submodule.disjoint_def.mpr
      intro v hs hu
      apply Prod.ext
      · exact Submodule.disjoint_def.mp (a.complementary z.1 hz.1).disjoint v.1 hs.1 hu.1
      · exact Submodule.disjoint_def.mp (b.complementary z.2 hz.2).disjoint v.2 hs.2 hu.2
    have disjoint := Submodule.disjoint_map (fiber z).injective prodDisjoint
  · apply eq_of_le_of_inf_le_of_le_sup stableLe
    · exact (disjoint.mono_right unstableLe).le_bot.trans bot_le
    · rw [(c.complementary z hz).sup_eq_top]
      exact le_top
  · apply eq_of_le_of_inf_le_of_le_sup unstableLe
    · exact (disjoint.symm.mono_right stableLe).le_bot.trans bot_le
    · rw [sup_comm,(c.complementary z hz).sup_eq_top]
      exact le_top

end ProductSplittingIdentification
end ConditionedStochasticStabilityHyperbolic.Paper
