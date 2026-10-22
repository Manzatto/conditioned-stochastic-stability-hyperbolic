module
public import LeanShared.Geometry.TangentChartTrivialization
public import LeanShared.Geometry.CoherentCenteredChartEquivalence
public import LeanShared.Analysis.ContinuousLinearFrameInverse
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual affine-normalized charts for a locally continuous tangent-frame
family. The ambient base distance and tangent norms are retained. -/
public noncomputable section
open Set Bundle IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.ContinuousCenteredFrameCharts
variable {X E P M : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

@[expose] def chartFrame (center p : M) (inside : p ∈ (chartAt E center).source)
    (A : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) p) : P ≃L[ℝ] E :=
  (A.trans ((CompactRiemannianChartBounds.chart_differentiable
    (chartAt E center) (chart_mem_maximalAtlas center)).mfderiv inside)).trans
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) ((chartAt E center) p))

theorem continuous_frame (center : M) (b : X → M)
    (inside : ∀ x, b x ∈ (chartAt E center).source)
    (A : ∀ x, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) (b x))
    (sections : ∀ v : P, Continuous (fun x =>
      (⟨b x, A x v⟩ : TangentBundle (𝓘(ℝ, E)) M))) :
    Continuous (fun x => (chartFrame center (b x) (inside x) (A x)).toContinuousLinearMap) := by
  let e := trivializationAt E (fun y : M => TangentSpace (𝓘(ℝ, E)) y) center
  have base (x : X) : b x ∈ e.baseSet := by
    rw [TangentChartTrivialization.baseSet]
    exact inside x
  apply continuous_clm_apply.mpr
  intro v
  have actual := (e.continuousOn.comp_continuous (sections v) (fun x => base x)).snd
  apply actual.congr
  intro x
  change (e (⟨b x, A x v⟩ : TangentBundle (𝓘(ℝ, E)) M)).2 = _
  rw [← e.continuousLinearMapAt_apply_of_mem ℝ (base x),
    TangentChartTrivialization.forward (inside x)]
  rfl

theorem continuous_inverse_frame (center : M) (b : X → M)
    (inside : ∀ x, b x ∈ (chartAt E center).source)
    (A : ∀ x, P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) (b x))
    (sections : ∀ v : P, Continuous (fun x =>
      (⟨b x, A x v⟩ : TangentBundle (𝓘(ℝ, E)) M))) :
    Continuous (fun x => (chartFrame center (b x) (inside x) (A x)).symm.toContinuousLinearMap) :=
  ContinuousLinearFrameInverse.continuous_inverse _ (continuous_frame center b inside A sections)

@[expose] def normalizedChart (center p : M) (inside : p ∈ (chartAt E center).source)
    (A : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) p) : OpenPartialHomeomorph M P :=
  (chartAt E center).transHomeomorph (CoherentCenteredCoordinateMaps.affineNormalize
    (chartFrame center p inside A) ((chartAt E center) p))

omit [FiniteDimensional ℝ P] in
theorem normalizedChart_source (center p : M) (inside : p ∈ (chartAt E center).source)
    (A : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) p) :
    (normalizedChart center p inside A).source = (chartAt E center).source := rfl

omit [FiniteDimensional ℝ P] in
theorem normalizedChart_center (center p : M) (inside : p ∈ (chartAt E center).source)
    (A : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) p) : normalizedChart center p inside A p = 0 := by
  change (chartFrame center p inside A).symm ((chartAt E center) p - (chartAt E center) p) = 0
  rw [sub_self, map_zero]

omit [FiniteDimensional ℝ P] in
theorem normalizedChart_decode_zero (center p : M) (inside : p ∈ (chartAt E center).source)
    (A : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) p) :
    (normalizedChart center p inside A).symm 0 = p := by
  change (chartAt E center).symm ((chartAt E center) p + chartFrame center p inside A 0) = p
  rw [map_zero, add_zero, (chartAt E center).left_inv inside]

end LeanShared.ContinuousCenteredFrameCharts
