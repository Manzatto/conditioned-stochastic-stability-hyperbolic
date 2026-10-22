module
public import LeanShared.Geometry.CompactManifoldPatchSubmersionVolume
public import LeanShared.Geometry.FiniteSmoothReferenceMeasure

/-! The finite smooth reference is constructed independently of every random
map and noise law. Literal C1/full control rank then produces uniform volume
domination, with no reference-volume comparison source. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set MeasureTheory IsManifold
open scoped ENNReal Topology ContDiff Manifold

theorem Data.uniform_submersion_volume_bound
    {E A M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace M] [BorelSpace M]
    (d : Data (E := E) (M := M)) (ρ : Measure A) [ρ.IsAddHaarMeasure]
    (ν : Measure E) [ν.IsAddHaarMeasure]
    {L O : Set A} (compactL : IsCompact L) (openO : IsOpen O) (contained : L ⊆ O)
    {H : M × A → M}
    (smooth : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, A))) (𝓘(ℝ, E)) 1 H (univ ×ˢ O))
    (rank : ∀ x : M, ∀ a ∈ L,
      Function.Surjective (mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, E)) (fun b => H (x, b)) a)) :
    ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧
      ∀ x : M, (ρ.restrict L).map (fun a => H (x, a)) ≤ C • d.measure ν := by
  apply ControlSubmersionCoordinates.exists_uniform_manifold_volume_bound_of_patches
    ρ ν (d.measure ν) _ compactL openO contained smooth rank
  intro p
  obtain ⟨x, hx, source, positive⟩ := d.cover p
  exact ⟨chartAt E x, d.density x, chart_mem_maximalAtlas x, source,
    (d.smooth x).continuous.continuousOn, positive, d.patch_le ν hx⟩

end LeanShared.FiniteSmoothReferenceCharts
