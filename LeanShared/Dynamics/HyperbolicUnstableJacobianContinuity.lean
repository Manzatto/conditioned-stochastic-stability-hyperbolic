module

public import LeanShared.Dynamics.HyperbolicContinuousKernelFrames
public import LeanShared.Dynamics.HyperbolicUnstableJacobian
public import LeanShared.Geometry.BundleFrameJacobianContinuity
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! The actual unstable Jacobian is continuous on the hyperbolic core.
The moving unstable frames, Gram volumes and derivative continuity are
all derived from the actual continuous splitting and C1 map. -/
public noncomputable section
open Set Filter Bundle IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.HyperbolicBasicSet
private theorem restriction_normDet_congr {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (D : U →L[ℝ] V) (P Q : Submodule ℝ U) (same : P=Q) :
    (D.toLinearMap.comp P.subtype).normDet=(D.toLinearMap.comp Q.subtype).normDet := by
  subst Q
  rfl
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (TangentSpace (𝓘(ℝ, E)) : M → Type _)]
  {T : M ≃ₜ M} {Λ : Set M}

theorem HyperbolicData.continuousOn_unstableJacobian (h : HyperbolicData (E := E) T Λ)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T) :
    ContinuousOn h.unstableJacobian Λ := by
  intro x hx
  obtain ⟨O,openO,member,H,frames⟩ := h.exists_continuous_kernel_frames x hx
  let K := Λ ∩ O
  let fibers : M → Type _ := TangentSpace (𝓘(ℝ, E))
  let A (y : K) : (h.projection y.val).ker →L[ℝ] fibers (T y.val) :=
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T y.val).comp (h.projection y.val).ker.subtypeL
  have imageContinuous (u : (h.projection x).ker) :
      Continuous (fun y : K => (⟨T y.val,A y (H y u)⟩ : TangentBundle (𝓘(ℝ, E)) M)) :=
    (forward.continuous_tangentMap (by rfl)).comp (frames u)
  have jacContinuous : Continuous (fun y : K => (A y).toLinearMap.normDet) := by
    apply continuousOn_univ.mp
    exact BundleFrameJacobianContinuity.continuousOn_normDet fibers fibers
      (fun y : K => y.val) (fun y : K => T y.val) univ
      (fun y : K => (h.projection y.val).ker) H A
      (fun u => (frames u).continuousOn) (fun u => (imageContinuous u).continuousOn)
  have actual (y : K) : h.unstableJacobian y.val=(A y).toLinearMap.normDet := by
    have forget : h.unstableJacobian y.val =
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T y.val).toLinearMap.comp
          (h.unstable y.val).subtype).normDet := by
      unfold HyperbolicData.unstableJacobian
      exact LinearMap.normDet_codRestrict _
    exact forget.trans (restriction_normDet_congr _ _ _
      (h.projection_kernel y.val y.property.1).symm)
  have continuousActual : Continuous (fun y : K => h.unstableJacobian y.val) :=
    jacContinuous.congr (fun y => (actual y).symm)
  have onK : ContinuousOn h.unstableJacobian K :=
    continuousOn_iff_continuous_domRestrict.mpr continuousActual
  exact (continuousWithinAt_inter (openO.mem_nhds member)).mp (onK x ⟨hx,member⟩)

end LeanShared.HyperbolicBasicSet
