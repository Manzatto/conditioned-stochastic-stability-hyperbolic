module

public import LeanShared.Geometry.CoherentCenteredLinearBounds
public import Mathlib.Topology.MetricSpace.Thickening
import all LeanShared.Geometry.CompactUniformCenteredCharts
public import Mathlib.Tactic.FieldSimp

/-! Uniformly small actual normalized coordinates stay in fixed compact
chart target patches, despite arbitrary pointwise frame/chart choices. -/
public noncomputable section
namespace LeanShared.CoherentCenteredCoordinateMaps
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff Bundle

set_option maxHeartbeats 1600000 in
theorem exists_compact_targets
    {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {H : M → M} {K : Set M} {B δ : ℝ}
    (d : CompactCoherentCenteredCharts.Data (E := E) (P := P) (Q := P) H K B δ)
    (frame : ∀ x : K, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x.val)
    (positiveB : 0 < B)
    (bounds : ∀ x, ‖(frame x).toContinuousLinearMap‖ ≤ B ∧
      ‖(frame x).symm.toContinuousLinearMap‖ ≤ B) :
    ∃ targets : K → Set E, (∀ i, IsCompact (targets i) ∧ targets i ⊆ (chartAt E i.val).target) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : K, ∀ z : P, ‖z‖ ≤ ρ →
        chart d x x.val + linear d frame x z ∈ targets (index d x) := by
  let A := fun i : K => (chartAt E i.val) '' d.patch i
  have compact (i : K) : IsCompact (A i) :=
    (d.compact i).image_of_continuousOn ((chartAt E i.val).continuousOn.mono (d.source i))
  have contained (i : K) : A i ⊆ (chartAt E i.val).target := by
    rintro y ⟨x, hx, rfl⟩
    exact (chartAt E i.val).map_source (d.source i hx)
  have witnesses (i : K) := (compact i).exists_cthickening_subset_open
    (chartAt E i.val).open_target (contained i)
  choose radii positive targetsInside using witnesses
  obtain ⟨τ, positiveτ, common⟩ := CompactUniformCenteredCharts.common_positive
    d.centers radii (fun i _ => positive i)
  obtain ⟨C, positiveC, bound⟩ := exists_uniform_linear_bound d frame positiveB bounds
  refine ⟨fun i => cthickening (radii i) (A i), fun i => ⟨(compact i).cthickening, targetsInside i⟩,
    τ / C, div_pos positiveτ positiveC, fun x z hz => ?_⟩
  have member : (chart d x) x.val ∈ A (index d x) :=
    mem_image_of_mem _ (interior_subset (index_spec d x).2)
  have distance : dist (chart d x x.val + linear d frame x z) (chart d x x.val) ≤ radii (index d x) := by
    rw [dist_eq_norm, add_sub_cancel_left]
    calc
      _ ≤ ‖(linear d frame x).toContinuousLinearMap‖ * ‖z‖ :=
        (linear d frame x).toContinuousLinearMap.le_opNorm z
      _ ≤ C * (τ / C) := mul_le_mul (bound x).1 hz (norm_nonneg z) positiveC.le
      _ = τ := by field_simp
      _ ≤ _ := common (index d x) (index_spec d x).1
  exact mem_cthickening_of_dist_le _ _ _ _ member distance

end LeanShared.CoherentCenteredCoordinateMaps
