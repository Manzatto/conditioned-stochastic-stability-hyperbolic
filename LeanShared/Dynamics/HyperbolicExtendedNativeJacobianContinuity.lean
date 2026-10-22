module
public import LeanShared.Dynamics.HyperbolicExtendedProjectionKernelFrames
public import LeanShared.Geometry.BundleFrameJacobianContinuity
public import LeanShared.Geometry.DiffeomorphismDifferential
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! The literal native principal-row determinant is continuous on the
constructed open collar for every actual C1 map. Local kernel frames and
both Gram volumes are constructed; determinant continuity is not input. -/
@[expose] public noncomputable section
open Set Filter Bundle IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.HyperbolicBasicSet.HyperbolicData.NormedAdaptedProjection
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}

theorem continuousOn_nativeJacobian (a : h.NormedAdaptedProjection)
    (f : M → M) (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 f) :
    ContinuousOn (fun x =>
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x).toLinearMap.domRestrict (a.unstable x)).normDet)
      a.collar := by
  intro x hx
  obtain ⟨O,openO,member,H,frames⟩ := a.exists_collar_kernel_frames x hx
  let K := a.collar ∩ O
  let fibers : M → Type _ := TangentSpace (𝓘(ℝ,E))
  let A (y : K) : (a.projection y.val).ker →L[ℝ] fibers (f y.val) :=
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f y.val).comp (a.projection y.val).ker.subtypeL
  have images (u : (a.projection x).ker) :
      Continuous (fun y : K => (⟨f y.val,A y (H y u)⟩ : TangentBundle (𝓘(ℝ,E)) M)) :=
    (regular.continuous_tangentMap (by rfl)).comp (frames u)
  have jacobian : Continuous (fun y : K => (A y).toLinearMap.normDet) := by
    apply continuousOn_univ.mp
    exact BundleFrameJacobianContinuity.continuousOn_normDet fibers fibers
      (fun y : K => y.val) (fun y : K => f y.val) univ
      (fun y : K => (a.projection y.val).ker) H A
      (fun u => (frames u).continuousOn) (fun u => (images u).continuousOn)
  have onK : ContinuousOn (fun y =>
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f y).toLinearMap.domRestrict (a.unstable y)).normDet) K :=
    continuousOn_iff_continuous_domRestrict.mpr jacobian
  exact (continuousWithinAt_inter (openO.mem_nhds member)).mp (onK x ⟨hx,member⟩)

omit [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem nativeJacobian_pos (a : h.NormedAdaptedProjection) (f : M ≃ₜ M)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) f)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) f.symm) (x : M) :
    0 < ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x).toLinearMap.domRestrict (a.unstable x)).normDet := by
  let D := DiffeomorphismDifferential.differential f forward inverse x
  have injective : Function.Injective
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x).toLinearMap.domRestrict (a.unstable x)) := by
    intro u v equal
    exact Subtype.ext (D.injective equal)
  have nonzero := (((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x).toLinearMap.domRestrict
    (a.unstable x)).normDet_ne_zero_tfae.out 5 1).mp injective
  exact lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm nonzero)

theorem continuousOn_nativeRatio (a : h.NormedAdaptedProjection) (f : M ≃ₜ M)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 f)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) f.symm)
    (w : M → ℝ) (continuous : Continuous w) :
    ContinuousOn (fun x => w x /
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x).toLinearMap.domRestrict (a.unstable x)).normDet)
      a.collar :=
  continuous.continuousOn.div (a.continuousOn_nativeJacobian f forward)
    (fun x _ => (a.nativeJacobian_pos f (forward.mdifferentiable one_ne_zero) inverse x).ne')

end LeanShared.HyperbolicBasicSet.HyperbolicData.NormedAdaptedProjection
