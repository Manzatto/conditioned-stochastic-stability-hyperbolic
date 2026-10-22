module
public import LeanShared.Dynamics.HyperbolicCoherentFrames
public import LeanShared.Dynamics.HyperbolicSplitCoordinates
import all LeanShared.Dynamics.HyperbolicSplitCoordinates
public import LeanShared.Analysis.IsometricSplitFrameBounds
public import LeanShared.Geometry.CompactRiemannianEndomorphisms

/-! Constructed pointwise Euclidean frames for an actual basic set, with
whole-frame bounds derived from the continuous invariant projection and the
continuous Riemannian metric. No continuous global trivialization or uniform
frame estimate is supplied. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

structure IsometricFraming (h : HyperbolicData (E := E) T Λ) where
  stableDimension : ℕ
  unstableDimension : ℕ
  dimensions : stableDimension + unstableDimension = Module.finrank ℝ E
  stable : ∀ x : Λ, EuclideanSpace ℝ (Fin stableDimension) ≃ₗᵢ[ℝ] h.stable x.val
  unstable : ∀ x : Λ, EuclideanSpace ℝ (Fin unstableDimension) ≃ₗᵢ[ℝ] h.unstable x.val

namespace IsometricFraming
variable {h : HyperbolicData (E := E) T Λ}

def whole (a : IsometricFraming h) (x : Λ) :
    (EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension)) ≃L[ℝ]
      TangentSpace (𝓘(ℝ, E)) x.val :=
  splitFrame _ _ (h.complementary x.val x.property).symm (a.unstable x) (a.stable x)

private theorem whole_apply_private (a : IsometricFraming h) (x : Λ)
    (z : EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension)) :
    a.whole x z = (a.unstable x z.1).val + (a.stable x z.2).val := rfl

theorem whole_apply (a : IsometricFraming h) (x : Λ)
    (z : EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension)) :
    a.whole x z = (a.unstable x z.1).val + (a.stable x z.2).val :=
  whole_apply_private a x z

theorem whole_bounds (a : IsometricFraming h) (x : Λ) :
    ‖(a.whole x).toContinuousLinearMap‖ ≤ 2 ∧
      ‖(a.whole x).symm.toContinuousLinearMap‖ ≤ 1 + ‖h.projection x.val‖ :=
  IsometricSplitFrameBounds.bounds _ _ (h.projection x.val)
    (h.projection_range x.val x.property) (h.projection_kernel x.val x.property)
    (h.projection_idempotent x.val x.property) (a.unstable x) (a.stable x)
    (a.whole x) (a.whole_apply x)

theorem exists_uniform_bound
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    (a : IsometricFraming h) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : Λ,
      ‖(a.whole x).toContinuousLinearMap‖ ≤ B ∧
      ‖(a.whole x).symm.toContinuousLinearMap‖ ≤ B := by
  obtain ⟨C, positiveC, bound⟩ := CompactRiemannianEndomorphisms.exists_norm_bound
    (F := E) (fun x : M => TangentSpace (𝓘(ℝ, E)) x) Λ h.compact h.projection h.continuous_splitting
  refine ⟨C + 3, by linarith, fun x => ⟨?_, ?_⟩⟩
  · exact (a.whole_bounds x).1.trans (by linarith)
  · exact (a.whole_bounds x).2.trans (by linarith [bound x.val x.property])

end IsometricFraming

theorem BasicData.exists_isometricFraming {V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm) :
    Nonempty (IsometricFraming b.hyperbolic) := by
  classical
  obtain ⟨ds, du, dimensions, frames⟩ := b.exists_euclidean_tangent_frames forward inverse
  exact ⟨{
    stableDimension := ds
    unstableDimension := du
    dimensions := dimensions
    stable := fun x => Classical.choice (frames x.val x.property).1
    unstable := fun x => Classical.choice (frames x.val x.property).2
  }⟩

end LeanShared.HyperbolicBasicSet
