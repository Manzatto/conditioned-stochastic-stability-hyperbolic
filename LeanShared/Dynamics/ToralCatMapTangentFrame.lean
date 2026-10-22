module

public import LeanShared.Dynamics.ToralCatMapSmooth
public import LeanShared.Geometry.UnitAddCircleFlatMetric
public import LeanShared.Geometry.LinearRechartedDifferential

/-! The actual torus tangent frame, assembled from the quotient circle
frames, the canonical product tangent splitting, and the actual Hilbert
rechart differential. -/

set_option maxHeartbeats 800000

@[expose] public noncomputable section
open Set IsManifold Bundle Function
open scoped Manifold ContDiff Bundle Topology
namespace LeanShared.ToralCatMap

abbrev LiftHilbert := WithLp 2 (ℝ × ℝ)

def liftHilbertEquivalence : (ℝ × ℝ) ≃L[ℝ] LiftHilbert :=
  LinearRechartedManifold.hilbertProductEquiv

def productTangentEquivalence (x : Torus) :
    TangentSpace (𝓘(ℝ, ProductModel)) x ≃L[ℝ]
      (TangentSpace (𝓘(ℝ, UnitAddCircleManifold.Model)) x.1 ×
        TangentSpace (𝓘(ℝ, UnitAddCircleManifold.Model)) x.2) := by
  exact ContinuousLinearEquiv.refl ℝ ProductModel

def productTangentFrame (x : Torus) : (ℝ × ℝ) ≃L[ℝ] TangentSpace (𝓘(ℝ, ProductModel)) x :=
  ((UnitAddCircleManifold.tangentFrame x.1).prodCongr
    (UnitAddCircleManifold.tangentFrame x.2)).trans (productTangentEquivalence x).symm

def tangentRechart (x : Torus) : TangentSpace (𝓘(ℝ, ProductModel)) x ≃L[ℝ]
    TangentSpace (𝓘(ℝ, HilbertModel)) x :=
  LinearRechartedManifold.identityDifferential hilbertEquivalence x

def tangentFrame (x : Torus) : LiftHilbert ≃L[ℝ] TangentSpace (𝓘(ℝ, HilbertModel)) x :=
  liftHilbertEquivalence.symm.trans ((productTangentFrame x).trans (tangentRechart x))

theorem tangentRechart_apply (x : Torus) (v : TangentSpace (𝓘(ℝ, ProductModel)) x) :
    tangentRechart x v = mfderiv (𝓘(ℝ, ProductModel)) (𝓘(ℝ, HilbertModel)) (@id Torus) x v := rfl

theorem tangentRechart_symm_apply (x : Torus) (v : TangentSpace (𝓘(ℝ, HilbertModel)) x) :
    (tangentRechart x).symm v = mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, ProductModel)) (@id Torus) x v := rfl

theorem continuous_product_frame :
    Continuous (fun p : Torus × (ℝ × ℝ) =>
      (⟨p.1, productTangentFrame p.1 p.2⟩ : TangentBundle (𝓘(ℝ, ProductModel)) Torus)) := by
  have circleFrame := FrameRiemannianMetric.continuous_frame
    (H := UnitAddCircleManifold.Model) UnitAddCircleManifold.tangentFrame
    UnitAddCircleManifold.continuous_frame_section
  have first : Continuous (fun p : Torus × (ℝ × ℝ) =>
      (⟨p.1.1, UnitAddCircleManifold.tangentFrame p.1.1 p.2.1⟩ :
        TangentBundle (𝓘(ℝ, UnitAddCircleManifold.Model)) UnitAddCircle)) :=
    circleFrame.comp (continuous_fst.fst.prodMk continuous_snd.fst)
  have second : Continuous (fun p : Torus × (ℝ × ℝ) =>
      (⟨p.1.2, UnitAddCircleManifold.tangentFrame p.1.2 p.2.2⟩ :
        TangentBundle (𝓘(ℝ, UnitAddCircleManifold.Model)) UnitAddCircle)) :=
    circleFrame.comp (continuous_fst.snd.prodMk continuous_snd.snd)
  have combine := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓘(ℝ, UnitAddCircleManifold.Model)) (M := UnitAddCircle)
    (I' := 𝓘(ℝ, UnitAddCircleManifold.Model)) (M' := UnitAddCircle) (n := 0)).continuous
  simpa only [← modelWithCornersSelf_prod] using! combine.comp (first.prodMk second)

theorem continuous_product_coframe :
    Continuous (fun p : TangentBundle (𝓘(ℝ, ProductModel)) Torus =>
      (productTangentFrame p.1).symm p.2) := by
  have split := (contMDiff_equivTangentBundleProd
    (I := 𝓘(ℝ, UnitAddCircleManifold.Model)) (M := UnitAddCircle)
    (I' := 𝓘(ℝ, UnitAddCircleManifold.Model)) (M' := UnitAddCircle) (n := 0)).continuous
  simpa only [← modelWithCornersSelf_prod] using!
    (UnitAddCircleManifold.continuous_coframe.comp split.fst).prodMk
      (UnitAddCircleManifold.continuous_coframe.comp split.snd)

theorem continuous_frame :
    Continuous (fun p : Torus × LiftHilbert =>
      (⟨p.1, tangentFrame p.1 p.2⟩ : TangentBundle (𝓘(ℝ, HilbertModel)) Torus)) := by
  have rechart := (identity_to_hilbert.contMDiff_tangentMap (m := 0) (by simp)).continuous
  have input := continuous_product_frame.comp
    (continuous_fst.prodMk (liftHilbertEquivalence.symm.continuous.comp continuous_snd))
  simpa only [tangentFrame, ContinuousLinearEquiv.trans_apply, tangentRechart_apply, tangentMap, id_eq]
    using! rechart.comp input

theorem continuous_coframe :
    Continuous (fun p : TangentBundle (𝓘(ℝ, HilbertModel)) Torus => (tangentFrame p.1).symm p.2) := by
  have rechart := (identity_from_hilbert.contMDiff_tangentMap (m := 0) (by simp)).continuous
  simpa only [tangentFrame, ContinuousLinearEquiv.symm_trans_apply, tangentRechart_symm_apply, tangentMap, id_eq]
    using! liftHilbertEquivalence.continuous.comp (continuous_product_coframe.comp rechart)

end LeanShared.ToralCatMap
