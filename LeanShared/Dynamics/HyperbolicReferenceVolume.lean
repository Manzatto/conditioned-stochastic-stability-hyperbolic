module

public import LeanShared.Dynamics.HyperbolicUnstableJacobianContinuity
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

/-! Actual unstable volume change under an immersion into Euclidean space.
The reference Jacobian is defined by the genuine differential Gram volumes.
Its logarithm differs from the supplied continuous-metric Jacobian by the
actual continuous unstable-volume coboundary. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Bundle IsManifold
open scoped Topology Manifold ContDiff
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

@[expose] def HyperbolicData.referenceUnstableVolume (h : HyperbolicData (E := E) T Λ)
    (f : M → F) (x : M) : ℝ :=
  ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x).toLinearMap.comp (h.unstable x).subtype).normDet

@[expose] def HyperbolicData.referenceUnstableJacobian (h : HyperbolicData (E := E) T Λ)
    (f : M → F) (x : M) : ℝ :=
  ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f (T x)).toLinearMap.comp
    ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T x).toLinearMap.comp (h.unstable x).subtype)).normDet /
    h.referenceUnstableVolume f x

omit [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem HyperbolicData.referenceUnstableVolume_positive (h : HyperbolicData (E := E) T Λ)
    (f : M → F) (injective : ∀ x, Function.Injective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x))
    (x : M) : 0 < h.referenceUnstableVolume f x := by
  apply lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm ?_)
  intro zero
  exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp zero)
    (LinearMap.ker_eq_bot.mpr ((injective x).comp (h.unstable x).subtype_injective))

omit [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem HyperbolicData.referenceUnstableJacobian_eq (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (f : M → F) (x : M) (hx : x ∈ Λ) :
    h.referenceUnstableJacobian f x =
      h.referenceUnstableVolume f (T x) * h.unstableJacobian x / h.referenceUnstableVolume f x := by
  let H := h.unstableDifferential forward inverse x hx
  let J := (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f (T x)).toLinearMap.comp (h.unstable (T x)).subtype
  have same : ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f (T x)).toLinearMap.comp
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T x).toLinearMap.comp (h.unstable x).subtype)) =
      J.comp H.toLinearMap := by
    ext v
    rfl
  unfold HyperbolicData.referenceUnstableJacobian
  rw [same, LinearMap.normDet_comp_of_finrank_eq _ _ H.toLinearEquiv.finrank_eq,
    ← h.unstableJacobian_eq_normDet forward inverse x hx]
  rfl

private theorem restriction_normDet_congr {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (D : U →L[ℝ] V) (P Q : Submodule ℝ U) (same : P = Q) :
    (D.toLinearMap.comp P.subtype).normDet = (D.toLinearMap.comp Q.subtype).normDet := by
  subst Q
  rfl

theorem HyperbolicData.continuousOn_referenceUnstableVolume (h : HyperbolicData (E := E) T Λ)
    (f : M → F) (smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 f) :
    ContinuousOn (h.referenceUnstableVolume f) Λ := by
  let _ : IsContinuousRiemannianBundle F (fun y : F => TangentSpace (𝓘(ℝ,F)) y) :=
    ⟨⟨(riemannianMetricVectorSpace F).inner, (riemannianMetricVectorSpace F).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  intro x hx
  obtain ⟨O, openO, member, H, frames⟩ := h.exists_continuous_kernel_frames x hx
  let K := Λ ∩ O
  let fibers : M → Type _ := TangentSpace (𝓘(ℝ,E))
  let targets : F → Type _ := TangentSpace (𝓘(ℝ,F))
  let A (y : K) : (h.projection y.val).ker →L[ℝ] targets (f y.val) :=
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f y.val).comp (h.projection y.val).ker.subtypeL
  have images (u : (h.projection x).ker) :
      Continuous (fun y : K => (⟨f y.val, A y (H y u)⟩ : TangentBundle (𝓘(ℝ,F)) F)) :=
    (smooth.continuous_tangentMap (by rfl)).comp (frames u)
  have volumes : Continuous (fun y : K => (A y).toLinearMap.normDet) := by
    apply continuousOn_univ.mp
    exact BundleFrameJacobianContinuity.continuousOn_normDet fibers targets
      (fun y : K => y.val) (fun y : K => f y.val) univ
      (fun y : K => (h.projection y.val).ker) H A
      (fun u => (frames u).continuousOn) (fun u => (images u).continuousOn)
  have actual (y : K) : h.referenceUnstableVolume f y.val = (A y).toLinearMap.normDet :=
    restriction_normDet_congr _ _ _ (h.projection_kernel y.val y.property.1).symm
  have continuousActual : Continuous (fun y : K => h.referenceUnstableVolume f y.val) :=
    volumes.congr (fun y => (actual y).symm)
  have onK : ContinuousOn (h.referenceUnstableVolume f) K :=
    continuousOn_iff_continuous_domRestrict.mpr continuousActual
  exact (continuousWithinAt_inter (openO.mem_nhds member)).mp (onK x ⟨hx, member⟩)

omit [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem HyperbolicData.log_referenceUnstableJacobian (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (f : M → F) (injective : ∀ x, Function.Injective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x))
    (x : M) (hx : x ∈ Λ) :
    Real.log (h.referenceUnstableJacobian f x) = Real.log (h.unstableJacobian x) +
      Real.log (h.referenceUnstableVolume f (T x)) - Real.log (h.referenceUnstableVolume f x) := by
  rw [h.referenceUnstableJacobian_eq forward inverse f x hx,
    Real.log_div (mul_ne_zero (h.referenceUnstableVolume_positive f injective (T x)).ne'
      (h.unstableJacobian_positive forward inverse x hx).ne')
      (h.referenceUnstableVolume_positive f injective x).ne',
    Real.log_mul (h.referenceUnstableVolume_positive f injective (T x)).ne'
      (h.unstableJacobian_positive forward inverse x hx).ne']
  ring

end LeanShared.HyperbolicBasicSet
