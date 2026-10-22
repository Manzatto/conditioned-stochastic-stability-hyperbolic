module
public import LeanShared.Dynamics.HyperbolicProjectionCoordinates
public import LeanShared.Geometry.BundleProjectionRangeCoordinates

/-! The local range frames constructed from the actual continuous hyperbolic
projection are frames of the genuine stable tangent fibers. In particular the
stable fiber dimension is locally constant on the hyperbolic set, without an
extra rank or global trivial-bundle hypothesis. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff

set_option maxHeartbeats 1600000 in
theorem HyperbolicData.exists_local_stable_fibre_frames
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (e : Trivialization E (Bundle.TotalSpace.proj (E := TangentSpace (𝓘(ℝ, E)))))
    [e.IsLinear ℝ] (x : M) (inside : x ∈ Λ ∩ e.baseSet) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ e.baseSet ∧
      ∀ y ∈ Λ ∩ U, Nonempty (h.stable x ≃L[ℝ] h.stable y) := by
  obtain ⟨U, openU, member, contained, frames⟩ := h.exists_local_coordinate_range_frames e x inside
  refine ⟨U, openU, member, contained, fun y hy => ?_⟩
  obtain ⟨matrixFrame⟩ := frames y hy
  let source := (ContinuousLinearEquiv.ofEq (h.stable x) (h.projection x).range
    (h.projection_range x inside.1).symm).trans
    (BundleEndomorphismCoordinates.rangeCoordinatesEquiv
      (TangentSpace (𝓘(ℝ, E))) e h.projection x inside.2)
  let target := (BundleEndomorphismCoordinates.rangeCoordinatesEquiv
    (TangentSpace (𝓘(ℝ, E))) e h.projection y (contained hy.2)).symm.trans
      (ContinuousLinearEquiv.ofEq (h.projection y).range (h.stable y) (h.projection_range y hy.1))
  exact ⟨source.trans (matrixFrame.trans target)⟩

set_option maxHeartbeats 1600000 in
theorem HyperbolicData.stable_finrank_locally_constant
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (x : M) (inside : x ∈ Λ) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ Λ ∩ U, Module.finrank ℝ (h.stable x) = Module.finrank ℝ (h.stable y) := by
  let e := trivializationAt E (TangentSpace (𝓘(ℝ, E))) x
  have linear : e.IsLinear ℝ := inferInstance
  have base : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  obtain ⟨U, openU, member, _, frames⟩ := h.exists_local_stable_fibre_frames e x ⟨inside, base⟩
  refine ⟨U, openU, member, fun y hy => ?_⟩
  exact (Classical.choice (frames y hy)).toLinearEquiv.finrank_eq

end LeanShared.HyperbolicBasicSet
