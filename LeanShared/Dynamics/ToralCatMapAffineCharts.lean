module

public import LeanShared.Dynamics.ToralCatMapDerivative
public import LeanShared.Geometry.SmoothInversePartialHomeomorph

/-! Actual affine quotient charts for the torus, proved compatible with
the smooth structure already constructed from the complex unit circle.
These charts retain the literal real quotient as inverse map. -/

set_option maxHeartbeats 800000
@[expose] public noncomputable section
open Set IsManifold Bundle Function
open scoped Manifold ContDiff Bundle Topology
namespace LeanShared.ToralCatMap

instance onePositive : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def localProjection (a : ℝ × ℝ) : OpenPartialHomeomorph (ℝ × ℝ) Torus :=
  (AddCircle.openPartialHomeomorphCoe (1 : ℝ) (a.1 - 1 / 2)).prod
    (AddCircle.openPartialHomeomorphCoe (1 : ℝ) (a.2 - 1 / 2))

theorem localProjection_coe (a : ℝ × ℝ) : (localProjection a : (ℝ × ℝ) → Torus) = quotient := rfl

theorem quotientDifferential_bijective (z : ℝ × ℝ) :
    Function.Bijective (mfderiv (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, HilbertModel)) quotient z) := by
  let A := (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).trans (realTangentFrame (quotient z))
  have equal : mfderiv (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, HilbertModel)) quotient z = A.toContinuousLinearMap := by
    ext v
    simpa only [A, realTangentFrame, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using
        quotientDifferential z ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z) v)
  rw [equal]
  exact A.bijective

theorem smooth_localProjection_inverse (a : ℝ × ℝ) :
    ContMDiffOn (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, ℝ × ℝ)) ∞
      (localProjection a).symm (localProjection a).target :=
  SmoothInversePartialHomeomorph.smooth_inverse (localProjection a)
    smooth_quotient.contMDiffOn (fun z _ => quotientDifferential_bijective z)

def circleCoordinateEquivalence : ℝ ≃L[ℝ] UnitAddCircleManifold.Model :=
  UnitAddCircleManifold.originDifferential.trans
    (tangentSpaceCastModel (𝓘(ℝ, UnitAddCircleManifold.Model)) (0 : UnitAddCircle))

def quotientCoordinateEquivalence : (ℝ × ℝ) ≃L[ℝ] HilbertModel :=
  (circleCoordinateEquivalence.prodCongr circleCoordinateEquivalence).trans hilbertEquivalence

def affineChart (a : ℝ × ℝ) : OpenPartialHomeomorph Torus HilbertModel :=
  (localProjection a).symm.trans quotientCoordinateEquivalence.toHomeomorph.toOpenPartialHomeomorph

theorem affineChart_mem_maximalAtlas (a : ℝ × ℝ) :
    affineChart a ∈ maximalAtlas (𝓘(ℝ, HilbertModel)) ∞ Torus := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · simpa only [affineChart, mfld_simps] using!
      quotientCoordinateEquivalence.contDiff.contMDiff.comp_contMDiffOn
        (smooth_localProjection_inverse a)
  · simpa only [affineChart, mfld_simps] using!
      (smooth_quotient.comp quotientCoordinateEquivalence.symm.contDiff.contMDiff).contMDiffOn

theorem affineChart_symm_apply (a : ℝ × ℝ) (v : HilbertModel) :
    (affineChart a).symm v = quotient (quotientCoordinateEquivalence.symm v) := rfl

theorem affineChart_quotient (a v : ℝ × ℝ) (member : v ∈ (localProjection a).source) :
    affineChart a (quotient v) = quotientCoordinateEquivalence v := by
  exact congrArg quotientCoordinateEquivalence ((localProjection a).left_inv member)

end LeanShared.ToralCatMap
