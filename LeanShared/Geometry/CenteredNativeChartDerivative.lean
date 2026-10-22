module
public import LeanShared.Geometry.CenteredAtlasCoordinates
public import LeanShared.Analysis.CenteredCoordinateBaseChange
public import LeanShared.Analysis.CenteredOffsetChange
public import LeanShared.Geometry.TangentChartTrivialization

/-! Exact native differential intertwining for fixed affine-normalized
charts at any actual orbit point, including off-core points and offsets. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold
namespace LeanShared.CenteredNativeChartDerivative
open CenteredManifoldCoordinates

theorem intertwines
    {E P M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace M] [ChartedSpace E M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    (H : M → M) (x : M) (c d : OpenPartialHomeomorph M E)
    (hc : c.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)))
    (hd : d.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)))
    (inside : x ∈ c.source) (target : H x ∈ d.source)
    (L R : P ≃L[ℝ] E) (a b : E)
    (smooth : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x)
    (v : TangentSpace (𝓘(ℝ,E)) x) :
    R.symm ((NormedSpace.fromTangentSpace (𝕜:=ℝ) (d (H x)))
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) d (H x)
        (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x v))) =
    fderiv ℝ (centered L R a b (d ∘ H ∘ c.symm)) (L.symm (c x-a))
      (L.symm ((NormedSpace.fromTangentSpace (𝕜:=ℝ) (c x))
        (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) c x v))) := by
  let C := (hc.mfderiv inside).trans (NormedSpace.fromTangentSpace (𝕜:=ℝ) (c x))
  let D := (hd.mfderiv target).trans (NormedSpace.fromTangentSpace (𝕜:=ℝ) (d (H x)))
  let e := L.trans C.symm
  let f := R.trans D.symm
  have sourceLinear : ((e.trans (hc.mfderiv inside)).trans
      (NormedSpace.fromTangentSpace (𝕜:=ℝ) (c x))) = L := by
    apply ContinuousLinearEquiv.ext
    funext z
    exact C.apply_symm_apply (L z)
  have targetLinear : ((f.trans (hd.mfderiv target)).trans
      (NormedSpace.fromTangentSpace (𝕜:=ℝ) (d (H x)))) = R := by
    apply ContinuousLinearEquiv.ext
    funext z
    exact D.apply_symm_apply (R z)
  have derivative := CenteredAtlasCoordinates.hasFDerivAt_centered H x c d hc hd
    inside target e f smooth
  rw [sourceLinear,targetLinear] at derivative
  change HasFDerivAt (centered L R (c x) (d (H x)) (d ∘ H ∘ c.symm)) _ 0 at derivative
  rw [fderiv_centered_source_change L R a (c x) b,
    fderiv_centered_offset L R (c x) b (d (H x)),derivative.fderiv]
  have cancel : e (L.symm (C v)) = v := by
    change C.symm (L (L.symm (C v))) = v
    rw [L.apply_symm_apply,C.symm_apply_apply]
  change R.symm (D (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x v)) =
    f.symm (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) H x (e (L.symm (C v))))
  rw [cancel]
  rfl

end LeanShared.CenteredNativeChartDerivative
