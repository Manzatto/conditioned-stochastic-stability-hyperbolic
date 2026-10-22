module
public import LeanShared.Dynamics.HyperbolicBasicSet
public import LeanShared.Geometry.BundleEndomorphismCoordinates
public import LeanShared.Analysis.CloseProjectionRanges

/-! Genuine local projection frames for the actual hyperbolic tangent bundle.
Operator-norm continuity and idempotence are derived from HyperbolicData's
continuous total-space splitting. Norm-close projection ranges then supply
local finite-dimensional frame equivalences; no globally trivial bundle or
constant-rank matrix source is assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Filter IsManifold Bundle
open scoped Topology Manifold ContDiff

set_option maxHeartbeats 1600000 in
theorem HyperbolicData.projection_coordinates_continuous
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (e : Trivialization E (Bundle.TotalSpace.proj (E := TangentSpace (𝓘(ℝ, E)))))
    [e.IsLinear ℝ] :
    ContinuousOn (BundleEndomorphismCoordinates.coordinates
      (TangentSpace (𝓘(ℝ, E))) e h.projection) (Λ ∩ e.baseSet) :=
  BundleEndomorphismCoordinates.continuousOn_coordinates
    (TangentSpace (𝓘(ℝ, E))) e h.projection Λ h.continuous_splitting

set_option maxHeartbeats 1600000 in
theorem HyperbolicData.projection_coordinates_idempotent
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (e : Trivialization E (Bundle.TotalSpace.proj (E := TangentSpace (𝓘(ℝ, E)))))
    [e.IsLinear ℝ] (x : M) (inside : x ∈ Λ ∩ e.baseSet) (v : E) :
    BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ, E))) e h.projection x
      (BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ, E))) e h.projection x v) =
      BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ, E))) e h.projection x v := by
  apply BundleEndomorphismCoordinates.coordinates_idempotent _ e h.projection x inside.2
  intro w
  have equality := congrArg (fun P => P w) (h.projection_idempotent x inside.1)
  simpa only [ContinuousLinearMap.comp_apply] using equality

set_option maxHeartbeats 1600000 in
theorem HyperbolicData.exists_local_coordinate_range_frames
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (e : Trivialization E (Bundle.TotalSpace.proj (E := TangentSpace (𝓘(ℝ, E)))))
    [e.IsLinear ℝ] (x : M) (inside : x ∈ Λ ∩ e.baseSet) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ e.baseSet ∧
      ∀ y ∈ Λ ∩ U, Nonempty
        ((BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ, E))) e h.projection x).range
          ≃L[ℝ]
        (BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ, E))) e h.projection y).range) := by
  let P : M → E →L[ℝ] E :=
    BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ, E))) e h.projection
  have continuous : ContinuousWithinAt P (Λ ∩ e.baseSet) x :=
    h.projection_coordinates_continuous e x inside
  have difference : ContinuousWithinAt (fun y => P y - P x) (Λ ∩ e.baseSet) x :=
    continuous.sub continuousWithinAt_const
  have center : ‖P x - P x‖ < (1 : ℝ) := by rw [sub_self, norm_zero]; exact zero_lt_one
  have near : ∀ᶠ y in 𝓝[Λ ∩ e.baseSet] x, ‖P y - P x‖ < 1 :=
    difference.norm.eventually (gt_mem_nhds center)
  obtain ⟨O, neighborhood, bound⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp near
  obtain ⟨V, contained, openV, member⟩ := mem_nhds_iff.mp neighborhood
  refine ⟨V ∩ e.baseSet, openV.inter e.open_baseSet, ⟨member, inside.2⟩,
    inter_subset_right, ?_⟩
  intro y hy
  have hy' : y ∈ Λ ∩ e.baseSet := ⟨hy.1, hy.2.2⟩
  refine ⟨CloseProjectionRanges.rangeEquiv (P x) (P y)
    (h.projection_coordinates_idempotent e x inside)
    (h.projection_coordinates_idempotent e y hy') ?_⟩
  have pointBound := bound ⟨contained hy.2.1, hy'⟩
  change ‖P y - P x‖ < 1 at pointBound
  simpa only [norm_sub_rev] using pointBound

end LeanShared.HyperbolicBasicSet
