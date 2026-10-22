module
public import LeanShared.Geometry.CoherentCenteredCoordinateMaps

/-! Actual dynamics in the coherently selected normalized charts. The local
maps, their zero reference orbit, recurrence identities, and small derivative
remainders are all derived from the constructed finite atlas output. -/
public noncomputable section
namespace LeanShared.CoherentCenteredCoordinateMaps
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

variable {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {H : M → M} {K : Set M} {B δ : ℝ}
  (d : CompactCoherentCenteredCharts.Data (E := E) (P := P) (Q := P) H K B δ)

@[expose] def advance (preserves : MapsTo H K K) (x : K) : K := ⟨H x.val, preserves x.property⟩

@[expose] def localMap (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (preserves : MapsTo H K K) (x : K) (z : P) : P :=
  coordinate d frame (advance preserves x) (H (decode d frame x z))

theorem localMap_zero (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (preserves : MapsTo H K K) (x : K) : localMap d frame preserves x 0 = 0 := by
  change coordinate d frame (advance preserves x) (H (decode d frame x 0)) = 0
  rw [decode_zero]
  exact coordinate_self d frame (advance preserves x)

theorem localMap_step (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (preserves : MapsTo H K K) (x : K) (y : M) (member : y ∈ (chart d x).source) :
    localMap d frame preserves x (coordinate d frame x y) =
      coordinate d frame (advance preserves x) (H y) := by
  change coordinate d frame (advance preserves x)
    (H (decode d frame x (coordinate d frame x y))) = _
  rw [decode_coordinate d frame x y member]

set_option maxHeartbeats 1600000 in
theorem localMap_estimates
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (preserves : MapsTo H K K)
    (forward : ∀ x, ‖(frame x).toContinuousLinearMap‖ ≤ B)
    (inverse : ∀ x, ‖(frame x).symm.toContinuousLinearMap‖ ≤ B)
    (x : K) (z : P) (small : ‖z‖ ≤ d.radius) :
    DifferentiableAt ℝ (localMap d frame preserves x) z ∧
      ‖fderiv ℝ (localMap d frame preserves x) z -
        (frame (advance preserves x)).symm.toContinuousLinearMap.comp
          ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (frame x).toContinuousLinearMap)‖ < δ := by
  have sourceMember := interior_subset (index_spec d x).2
  have targetMember := interior_subset (index_spec d (advance preserves x)).2
  have estimate := d.estimates (index d x) (index_spec d x).1
    (index d (advance preserves x)) (index_spec d (advance preserves x)).1
    x.val sourceMember targetMember (frame x) (frame (advance preserves x))
    (forward x) (inverse (advance preserves x))
  dsimp only at estimate
  have result := estimate z small
  exact ⟨result.2.2.1, result.2.2.2⟩

end LeanShared.CoherentCenteredCoordinateMaps
