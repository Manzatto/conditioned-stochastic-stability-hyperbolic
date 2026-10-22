module

public import LeanShared.Dynamics.HyperbolicReferenceVolume
public import LeanShared.Dynamics.HyperbolicFiniteNativeChartBlocks
public import LeanShared.Geometry.NativeChartVectorDerivative
public import LeanShared.Geometry.FlatTangentIsometry
public import LeanShared.Geometry.BundleKernelFrameRatio
public import LeanShared.Geometry.MovingKernelLogJacobian

/-! The actual unstable reference Jacobian equals the genuine moving-kernel
Gram ratio of the two literal coordinate derivatives f∘T and f. No
isometry of the source chart or moving determinant identity is assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Bundle IsManifold
open scoped Manifold ContDiff Bundle
variable {E F M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

private theorem normalized_normDet {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] (y : F) (D : U →L[ℝ] TangentSpace (𝓘(ℝ,F)) y) :
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) y).toContinuousLinearMap.comp D).toLinearMap.normDet =
      D.toLinearMap.normDet :=
  NormDetIsometry.comp D.toLinearMap (FlatTangentIsometry.equivalence y).toLinearIsometry

private theorem restriction_normDet_congr {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (D : U →L[ℝ] V) (P Q : Submodule ℝ U) (same : P = Q) :
    (D.toLinearMap.comp P.subtype).normDet = (D.toLinearMap.comp Q.subtype).normDet := by
  subst Q
  rfl

set_option maxHeartbeats 1600000 in
theorem HyperbolicData.referenceUnstableJacobian_coordinate_ratio (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (f : M → F) (differentiable : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,F)) f)
    (i : Λ) (x : M) (hx : x ∈ Λ) (source : x ∈ (chartAt E i.val).source) :
    h.referenceUnstableJacobian f x = MovingKernelLogJacobian.ratio (h.chartProjection i x)
      (NativeChartVectorDerivative.coordinateDifferential (f ∘ T) i.val x)
      (NativeChartVectorDerivative.coordinateDifferential f i.val x) := by
  let fibers : M → Type _ := TangentSpace (𝓘(ℝ,E))
  let e := trivializationAt E fibers i.val
  let A : fibers x →L[ℝ] F :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (T x))).toContinuousLinearMap.comp
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) (f ∘ T) x)
  let B : fibers x →L[ℝ] F :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).toContinuousLinearMap.comp
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x)
  have chain := mfderiv_comp x (differentiable (T x)) (forward x)
  have numerator :
      (((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f (T x)).toLinearMap.comp
        ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T x).toLinearMap.comp (h.unstable x).subtype))).normDet =
        (A.comp (h.projection x).ker.subtypeL).toLinearMap.normDet := by
    have native : ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) (f ∘ T) x).comp (h.unstable x).subtypeL).toLinearMap =
        (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f (T x)).toLinearMap.comp
          ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T x).toLinearMap.comp (h.unstable x).subtype) := by
      rw [chain]
      rfl
    rw [← native, ← normalized_normDet (f (T x))]
    exact restriction_normDet_congr A (h.unstable x) (h.projection x).ker (h.projection_kernel x hx).symm
  have denominator : h.referenceUnstableVolume f x = (B.comp (h.projection x).ker.subtypeL).toLinearMap.normDet := by
    unfold HyperbolicData.referenceUnstableVolume
    change ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x).comp (h.unstable x).subtypeL).toLinearMap.normDet = _
    rw [← normalized_normDet (f x)]
    exact restriction_normDet_congr B (h.unstable x) (h.projection x).ker (h.projection_kernel x hx).symm
  have inside : x ∈ e.baseSet := by
    rw [TangentChartTrivialization.baseSet]
    exact source
  unfold HyperbolicData.referenceUnstableJacobian
  rw [numerator, denominator]
  exact BundleEndomorphismCoordinates.kernel_ratio_coordinates fibers e h.projection x inside A B

end LeanShared.HyperbolicBasicSet
