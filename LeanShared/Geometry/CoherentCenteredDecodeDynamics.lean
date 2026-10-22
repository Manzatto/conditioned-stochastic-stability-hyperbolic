module

public import LeanShared.Geometry.CoherentCenteredMapDynamics

/-! Small coordinate orbit steps decode to literal manifold dynamics. -/
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

theorem decode_localMap
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (preserves : MapsTo H K K)
    (forward : ∀ x, ‖(frame x).toContinuousLinearMap‖ ≤ B)
    (inverse : ∀ x, ‖(frame x).symm.toContinuousLinearMap‖ ≤ B)
    (x : K) (z : P) (small : ‖z‖ ≤ d.radius) :
    decode d frame (advance preserves x) (localMap d frame preserves x z) =
      H (decode d frame x z) := by
  have estimate := d.estimates (index d x) (index_spec d x).1
    (index d (advance preserves x)) (index_spec d (advance preserves x)).1
    x.val (interior_subset (index_spec d x).2)
    (interior_subset (index_spec d (advance preserves x)).2)
    (frame x) (frame (advance preserves x)) (forward x) (inverse (advance preserves x)) z small
  exact decode_coordinate d frame (advance preserves x) _ estimate.2.1

end LeanShared.CoherentCenteredCoordinateMaps
