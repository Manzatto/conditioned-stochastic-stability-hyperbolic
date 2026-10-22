module
public import LeanShared.MeasureTheory.ImmersionAtlasVolume
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Data.Set.Countable

/-! A genuine C¹ manifold atlas supplies all the coordinate data used by the
independent induced-volume construction. No measure or area theorem is input. -/
public noncomputable section
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.ImmersionVolumeAtlas
variable {U E M : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace U M] [IsManifold (𝓘(ℝ, U)) 1 M]
  [SecondCountableTopology M] [Nonempty M]

omit [MeasurableSpace U] [BorelSpace U] [MeasurableSpace M] [BorelSpace M] in
theorem exists_atlas (ι : M → E) (smooth : ContMDiff (𝓘(ℝ, U)) (𝓘(ℝ, E)) 1 ι) :
    ∃ A : ImmersionAtlasVolume.Atlas (U := U) ι,
      ∀ n, A.chart n ∈ maximalAtlas (𝓘(ℝ, U)) 1 M := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace U M
  have : SigmaCompactSpace M := inferInstance
  obtain ⟨s, countable, covers⟩ : ∃ s : Set M, s.Countable ∧
      ⋃ (x) (_ : x ∈ s), (chartAt U x).source = univ :=
    countable_cover_nhds_of_sigmaCompact (fun x : M => chart_source_mem_nhds U x)
  have nonempty : s.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty M›
    have mem : x ∈ ⋃ (y) (_ : y ∈ s), (chartAt U y).source := by rw [covers]; trivial
    rcases mem_iUnion.mp mem with ⟨y, hy⟩
    rcases mem_iUnion.mp hy with ⟨hys, _⟩
    exact ⟨y, hys⟩
  obtain ⟨c, rangeC⟩ := countable.exists_eq_range nonempty
  have cover : ⋃ n, (chartAt U (c n)).source = univ := by
    ext z
    simp only [mem_iUnion, mem_univ, iff_true]
    have hz : z ∈ ⋃ (y) (_ : y ∈ s), (chartAt U y).source := by rw [covers]; trivial
    rcases mem_iUnion.mp hz with ⟨y, hy⟩
    rcases mem_iUnion.mp hy with ⟨hys, hzy⟩
    rw [rangeC] at hys
    obtain ⟨n, rfl⟩ := hys
    exact ⟨n, hzy⟩
  refine ⟨⟨(fun n => chartAt U (c n)), cover, ?_, ?_⟩,
    fun n => chart_mem_maximalAtlas (c n)⟩
  · intro n
    have globalSmooth : ContMDiffOn (𝓘(ℝ, U)) (𝓘(ℝ, E)) 1 ι univ :=
      smooth.contMDiffOn
    exact (globalSmooth.comp
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, U)) (x := c n)) (fun _ _ => mem_univ _)).contDiffOn
  · intro i j
    have hi := contMDiffOn_chart_symm (I := 𝓘(ℝ, U)) (n := (1 : ℕ∞ω)) (x := c i)
    have hj := contMDiffOn_chart (I := 𝓘(ℝ, U)) (n := (1 : ℕ∞ω)) (x := c j)
    exact (hj.comp (hi.mono (fun _ h => h.1)) (fun _ h => h.2)).contDiffOn
end LeanShared.ImmersionVolumeAtlas
