module
public import LeanShared.MeasureTheory.CoordinatePatchMeasure
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Compactness.Compact

/-! A compact manifold has a finite collection of genuine coordinate patches
with compactly supported smooth densities positive at every point in at least
one patch. The densities and finite cover are constructed. -/
public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold
namespace LeanShared.FiniteSmoothReferenceCharts
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [CompactSpace M]
  [ChartedSpace E M]

structure Data where
  index : Finset M
  density : M → E → ℝ
  support : ∀ x, tsupport (density x) ⊆ (chartAt E x).target
  compact_support : ∀ x, HasCompactSupport (density x)
  smooth : ∀ x, ContDiff ℝ ∞ (density x)
  bounds : ∀ x y, density x y ∈ Icc 0 1
  cover : ∀ p : M, ∃ x ∈ index, p ∈ (chartAt E x).source ∧ 0 < density x (chartAt E x p)

theorem exists_data : Nonempty (Data (E := E) (M := M)) := by
  classical
  have bump (x : M) : ∃ f : E → ℝ,
      tsupport f ⊆ (chartAt E x).target ∧ HasCompactSupport f ∧ ContDiff ℝ ∞ f ∧
      range f ⊆ Icc 0 1 ∧ f (chartAt E x x) = 1 :=
    exists_contDiff_tsupport_subset ((chartAt E x).open_target.mem_nhds
      ((chartAt E x).map_source (mem_chart_source E x)))
  let f : M → E → ℝ := fun x => Classical.choose (bump x)
  have facts (x : M) := Classical.choose_spec (bump x)
  let V (x : M) : Set M := (chartAt E x).source ∩
    (chartAt E x) ⁻¹' {y | 0 < f x y}
  have openV (x : M) : IsOpen (V x) := by
    exact (chartAt E x).continuousOn.isOpen_inter_preimage
      (chartAt E x).open_source (isOpen_lt continuous_const (facts x).2.2.1.continuous)
  have member (x : M) : x ∈ V x := by
    refine ⟨mem_chart_source E x, ?_⟩
    change 0 < (Classical.choose (bump x)) (chartAt E x x)
    rw [(facts x).2.2.2.2]
    exact zero_lt_one
  obtain ⟨s, cover⟩ := isCompact_univ.elim_finite_subcover V openV (by
    intro x _
    exact mem_iUnion.mpr ⟨x, member x⟩)
  refine ⟨⟨s, f, fun x => (facts x).1, fun x => (facts x).2.1,
    fun x => (facts x).2.2.1, fun x y => (facts x).2.2.2.1 ⟨y, rfl⟩, ?_⟩⟩
  intro p
  rcases mem_iUnion.mp (cover (mem_univ p)) with ⟨x, hx⟩
  rcases mem_iUnion.mp hx with ⟨hx, hp⟩
  exact ⟨x, hx, hp⟩

end LeanShared.FiniteSmoothReferenceCharts
