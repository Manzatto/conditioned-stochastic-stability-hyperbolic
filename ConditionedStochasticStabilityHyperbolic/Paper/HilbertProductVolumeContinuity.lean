module

public import ConditionedStochasticStabilityHyperbolic.Paper.HilbertProductUnstableProjection
public import LeanShared.Geometry.HilbertProductDifferential
public import LeanShared.Geometry.HilbertSubmoduleBundleNormDetContinuity
public import LeanShared.Dynamics.HyperbolicContinuousUnstableFrames
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! The actual product unstable-volume correction is continuous in arbitrary
continuous Riemannian metrics. Smooth projection derivatives and constructed
unstable frames supply its Gram-volume formula; no continuity of the product
fiber identification is assumed. -/
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
local instance hilbertProductVolumeContinuityLocal1 : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hilbertProductVolumeContinuityLocal2 : IsManifold (𝓘(ℝ, WithLp 2 (E × F))) ∞ (X × Y) :=
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

@[expose] def unstableVolume (p : ProductSplittingIdentification a b c) (z : X × Y) : ℝ :=
  by
    classical
    exact if hz : z ∈ K ×ˢ L then (p.unstableFiber a b c z hz).toLinearMap.normDet else 1

set_option maxHeartbeats 1600000 in
theorem continuousOn_unstableVolume (p : ProductSplittingIdentification a b c) :
    ContinuousOn (p.unstableVolume a b c) (K ×ˢ L) := by
  classical
  intro z hz
  obtain ⟨O,openO,member,H,frames⟩ := c.exists_continuous_unstable_frames z hz
  let V := (K ×ˢ L) ∩ O
  let fibers := (TangentSpace (𝓘(ℝ,WithLp 2 (E × F))) : X × Y → Type _)
  let Fm (y : V) := (c.unstable y.val).subtypeL.comp (H y).toContinuousLinearMap
  let J (y : V) := (p.unstableFiber a b c y.val y.property.1).symm
  let B (y : V) := (J y).toContinuousLinearMap.comp (H y).toContinuousLinearMap
  have denominator : Continuous (fun y : V => (Fm y).toLinearMap.normDet) := by
    apply continuousOn_univ.mp
    exact BundleNormDetContinuity.continuousOn_normDet fibers (fun y : V => y.val) univ Fm
      (fun u => (frames u).continuousOn)
  have first (u : c.unstable z) : Continuous
      (fun y : V => (⟨y.val.1,(B y u).fst.val⟩ : TangentBundle (𝓘(ℝ,E)) X)) := by
    have actual := (HilbertProductDifferential.smooth_fst (E := E) (F := F) (X := X) (Y := Y)).continuous_tangentMap (by simp)
      |>.comp (frames u)
    apply actual.congr
    intro y
    exact congrArg (fun v => (⟨y.val.1,v⟩ : TangentBundle (𝓘(ℝ,E)) X))
      (p.unstableFiber_symm_fst a b c y.val y.property.1 (H y u)).symm
  have second (u : c.unstable z) : Continuous
      (fun y : V => (⟨y.val.2,(B y u).snd.val⟩ : TangentBundle (𝓘(ℝ,F)) Y)) := by
    have actual := (HilbertProductDifferential.smooth_snd (E := E) (F := F) (X := X) (Y := Y)).continuous_tangentMap (by simp)
      |>.comp (frames u)
    apply actual.congr
    intro y
    exact congrArg (fun v => (⟨y.val.2,v⟩ : TangentBundle (𝓘(ℝ,F)) Y))
      (p.unstableFiber_symm_snd a b c y.val y.property.1 (H y u)).symm
  have numerator : Continuous (fun y : V => (B y).toLinearMap.normDet) := by
    apply continuousOn_univ.mp
    exact HilbertSubmoduleBundleNormDetContinuity.continuousOn_normDet
      (TangentSpace (𝓘(ℝ,E)) : X → Type _) (TangentSpace (𝓘(ℝ,F)) : Y → Type _)
      (fun y : V => y.val.1) (fun y : V => y.val.2) univ
      (fun y : V => a.unstable y.val.1) (fun y : V => b.unstable y.val.2) B
      (fun u => (first u).continuousOn) (fun u => (second u).continuousOn)
  have nonzero (y : V) : (Fm y).toLinearMap.normDet ≠ 0 := by
    intro zero
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp zero)
      (LinearMap.ker_eq_bot.mpr (Subtype.val_injective.comp (H y).injective))
  have inverseFormula (y : V) : (J y).toLinearMap.normDet=
      (B y).toLinearMap.normDet/(Fm y).toLinearMap.normDet := by
    have volume : (Fm y).toLinearMap.normDet=(H y).toLinearMap.normDet := by
      exact (LinearMap.normDet_codRestrict (fun u => (H y u).property)).symm
    have composition := LinearMap.normDet_comp_of_finrank_eq
      (H y).toLinearMap (J y).toLinearMap (H y).toLinearEquiv.finrank_eq
    change (J y).toLinearMap.normDet=((J y).toLinearMap.comp (H y).toLinearMap).normDet/_
    rw [composition,←volume,mul_div_cancel_right₀ _ (nonzero y)]
  have inverseContinuous : Continuous (fun y : V => (J y).toLinearMap.normDet) :=
    (numerator.div denominator nonzero).congr (fun y => (inverseFormula y).symm)
  have inverseNonzero (y : V) : (J y).toLinearMap.normDet ≠ 0 := by
    intro zero
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp zero)
      (LinearMap.ker_eq_bot.mpr (J y).injective)
  have formula (y : V) : p.unstableVolume a b c y.val=1/(J y).toLinearMap.normDet := by
    rw [unstableVolume,dite_eq_left y.property.1]
    let A := p.unstableFiber a b c y.val y.property.1
    have composition := LinearMap.normDet_comp_of_finrank_eq
      A.toLinearMap A.symm.toLinearMap A.toLinearEquiv.finrank_eq
    have identity : A.symm.toLinearMap.comp A.toLinearMap=LinearMap.id := by ext v; simp
    rw [identity,LinearMap.normDet_id] at composition
    apply (eq_div_iff (inverseNonzero y)).mpr
    exact (mul_comm _ _).trans composition.symm
  have volumeContinuous : Continuous (fun y : V => p.unstableVolume a b c y.val) :=
    (continuous_const.div inverseContinuous inverseNonzero).congr (fun y => (formula y).symm)
  have onV : ContinuousOn (p.unstableVolume a b c) V :=
    continuousOn_iff_continuous_domRestrict.mpr volumeContinuous
  exact (continuousWithinAt_inter (openO.mem_nhds member)).mp (onV z ⟨hz,member⟩)

end ProductSplittingIdentification
end ConditionedStochasticStabilityHyperbolic.Paper
