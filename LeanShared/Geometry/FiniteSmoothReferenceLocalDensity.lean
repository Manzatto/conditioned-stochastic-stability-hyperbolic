module
public import LeanShared.Geometry.FiniteSmoothReferenceMeasure
public import LeanShared.MeasureTheory.CoordinateJacobianDensityProperties
public import LeanShared.MeasureTheory.CoordinateJacobianDensityMeasure
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! The finite chart-bump reference has a genuine positive continuous density
in EVERY ordinary smooth chart. Its local density is constructed as the sum
of inverse-transition Jacobian densities. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set IsManifold
open scoped Topology Manifold ContDiff

@[expose] def Data.localDensity
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (d : Data (E := E) (M := M)) (c : OpenPartialHomeomorph M E) (y : E) : ℝ :=
  ∑ x ∈ d.index, CoordinateJacobianDensity.density (chartAt E x) c (d.density x) y

private theorem transition_regular
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (e c : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) :
    ContDiffOn ℝ 1 (e.symm.trans c).symm (e.symm.trans c).target := by
  have first := (contMDiffOn_symm_of_mem_maximalAtlas hc).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have last := (contMDiffOn_of_mem_maximalAtlas he).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have raw : ContMDiffOn (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (e ∘ c.symm) (e.symm.trans c).target :=
    last.comp (first.mono (fun _ h => h.1)) (fun _ h => h.2)
  simpa only [OpenPartialHomeomorph.coe_trans_symm,OpenPartialHomeomorph.symm_symm] using raw.contDiffOn

theorem Data.localDensity_continuousOn
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) : ContinuousOn (d.localDensity c) c.target := by
  apply continuousOn_finsetSum
  intro x _
  exact CoordinateJacobianDensity.continuousOn (chartAt E x) c (d.density x)
    (transition_regular _ _ (chart_mem_maximalAtlas x) hc) (d.smooth x).continuous
    (d.compact_support x) (d.support x)

theorem Data.localDensity_nonnegative
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (d : Data (E := E) (M := M)) (c : OpenPartialHomeomorph M E) (y : E) :
    0 ≤ d.localDensity c y := by
  exact Finset.sum_nonneg (fun x _ => CoordinateJacobianDensity.nonnegative _ _ _ (fun z => (d.bounds x z).1) y)

theorem Data.localDensity_positive
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (d : Data (E := E) (M := M)) (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (y : E) (inside : y ∈ c.target) :
    0 < d.localDensity c y := by
  obtain ⟨x,member,source,positive⟩ := d.cover (c.symm y)
  have value : 0 < CoordinateJacobianDensity.density (chartAt E x) c (d.density x) y := by
    apply CoordinateJacobianDensity.positive _ _ (chart_mem_maximalAtlas x) hc _ y ⟨inside,source⟩
    exact positive
  exact value.trans_le (Finset.single_le_sum
    (fun i _ => CoordinateJacobianDensity.nonnegative _ _ _ (fun z => (d.bounds i z).1) y) member)

end LeanShared.FiniteSmoothReferenceCharts
