module
public import LeanShared.Geometry.CenteredManifoldCoordinates
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! Centered coordinates in chosen actual atlas charts. Unlike chartAt at a
moving center, these charts may be fixed on a finite compact cover. Their
actual differentials normalize arbitrary tangent frames at the center. -/
public noncomputable section
namespace LeanShared.CenteredAtlasCoordinates
open Set IsManifold
open scoped Manifold
open LeanShared.CenteredManifoldCoordinates

theorem hasFDerivAt_centered
    {E F P Q M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace N] [ChartedSpace F N]
    (H : M → N) (x : M)
    (c : OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph N F)
    (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)))
    (hd : d.MDifferentiable (𝓘(ℝ, F)) (𝓘(ℝ, F)))
    (inside : x ∈ c.source) (target : H x ∈ d.source)
    (e : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x)
    (f : Q ≃L[ℝ] TangentSpace (𝓘(ℝ, F)) (H x))
    (smooth : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) H x) :
    HasFDerivAt
      (centered
        ((e.trans (hc.mfderiv inside)).trans (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x)))
        ((f.trans (hd.mfderiv target)).trans (NormedSpace.fromTangentSpace (𝕜 := ℝ) (d (H x))))
        (c x) (d (H x)) (fun y => d (H (c.symm y))))
      (f.symm.toContinuousLinearMap.comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) H x).comp e.toContinuousLinearMap)) 0 := by
  let C := hc.mfderiv inside
  let D := hd.mfderiv target
  have value : c.symm (c x) = x := c.left_inv inside
  have source : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) c.symm (c x)
      C.symm.toContinuousLinearMap :=
    (hc.mdifferentiableAt_symm (c.map_source inside)).hasMFDerivAt
  have middle_at : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) H (c.symm (c x))
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) H x) := by
    rw [value]
    exact smooth.hasMFDerivAt
  have middle := middle_at.comp (c x) source
  have last_at : HasMFDerivAt (𝓘(ℝ, F)) (𝓘(ℝ, F)) d (H (c.symm (c x)))
      D.toContinuousLinearMap := by
    rw [value]
    exact (hd.mdifferentiableAt target).hasMFDerivAt
  have raw := (last_at.comp (c x) middle).hasFDerivAt
  have normalized := centered_hasFDerivAt
    ((e.trans C).trans (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x)))
    ((f.trans D).trans (NormedSpace.fromTangentSpace (𝕜 := ℝ) (d (H x))))
    (c x) (d (H x)) _ _ raw
  convert normalized using 1
  · rfl
  · ext v
    change f.symm (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) H x (e v)) =
      f.symm (D.symm (D
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) H x (C.symm (C (e v))))))
    rw [D.symm_apply_apply, C.symm_apply_apply]

end LeanShared.CenteredAtlasCoordinates
