module
public import LeanShared.Geometry.AtlasPatchSubmersionVolume
public import LeanShared.Analysis.CompactParametricVolumeCover

/-! Uniform pushforward domination for compact manifold random endpoints is
proved from literal C1/control rank and an actual positive smooth-volume chart
description. No density, domination constant, or chart cover is supplied. -/
public noncomputable section
namespace LeanShared.ControlSubmersionCoordinates
open Set MeasureTheory IsManifold
open scoped ENNReal Topology ContDiff Manifold

theorem exists_uniform_manifold_volume_bound_of_patches
    {E A M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace M] [BorelSpace M]
    (ρ : Measure A) [ρ.IsAddHaarMeasure] (ν : Measure E) [ν.IsAddHaarMeasure] (σ : Measure M)
    (reference : ∀ p : M, ∃ e : OpenPartialHomeomorph M E, ∃ r : E → ℝ,
      e ∈ maximalAtlas (𝓘(ℝ, E)) 1 M ∧ p ∈ e.source ∧
      ContinuousOn r e.target ∧ 0 < r (e p) ∧
      CoordinatePatchMeasure.patch e ν (fun y => ENNReal.ofReal (r y)) ≤ σ)
    {L O : Set A} (compactL : IsCompact L) (openO : IsOpen O) (contained : L ⊆ O)
    {H : M × A → M}
    (smooth : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, A))) (𝓘(ℝ, E)) 1 H (univ ×ˢ O))
    (rank : ∀ x : M, ∀ a ∈ L,
      Function.Surjective (mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, E)) (fun b => H (x, b)) a)) :
    ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∀ x : M, (ρ.restrict L).map (fun a => H (x, a)) ≤ C • σ := by
  have atPoint (x : M) (a : A) (ha : a ∈ L) :
      ContMDiffAt ((𝓘(ℝ, E)).prod (𝓘(ℝ, A))) (𝓘(ℝ, E)) 1 H (x, a) :=
    (smooth (x, a) ⟨mem_univ _, contained ha⟩).contMDiffAt
      ((isOpen_univ.prod openO).mem_nhds ⟨mem_univ _, contained ha⟩)
  have measurable (x : M) (_hx : x ∈ (univ : Set M)) :
      AEMeasurable (fun a => H (x, a)) (ρ.restrict L) := by
    apply ContinuousOn.aemeasurable₀ _ compactL.measurableSet.nullMeasurableSet
    intro a ha
    exact ((atPoint x a ha).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have localBound (x : M) (_hx : x ∈ (univ : Set M)) (a : A) (ha : a ∈ L) :
      ∃ U : Set M, ∃ V : Set A, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ a ∈ V ∧
        ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∀ y ∈ U, ∀ B : Set M, MeasurableSet B →
          ρ ((fun b => H (y, b)) ⁻¹' B ∩ V) ≤ C * σ B := by
    obtain ⟨e, r, atlas, source, continuousR, positiveR, patchBound⟩ := reference (H (x, a))
    exact exists_local_atlas_patch_volume_bound ρ ν σ (atPoint x a ha) (rank x a ha)
      e atlas source r patchBound continuousR positiveR
  obtain ⟨C, finiteC, bound⟩ := CompactParametricVolumeCover.exists_uniform_bound
    ρ σ isCompact_univ compactL measurable localBound
  exact ⟨C, finiteC, fun x => bound x (mem_univ _)⟩

end LeanShared.ControlSubmersionCoordinates
