module
public import LeanShared.Dynamics.PeriodicChartDerivative
public import LeanShared.Geometry.FractionalChartHolderCompact
public import LeanShared.Geometry.FractionalOneJetIteration
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Uniform constants for chart chains along a compact hyperbolic set. A finite family
of smooth charts with open domains whose closures lie in the chart sources, and compact
marked subsets of the domains, is fixed. For a `C^(1+α)` map `H` the chart
representatives `φ_j ∘ H ∘ φ_i⁻¹` have uniformly bounded, uniformly `α`-Hölder derivatives
on the compact pieces `{y ∈ φ_i(closure D_i) | H(φ_i⁻¹ y) ∈ closure D_j}`, and the chart
differentials are uniformly bounded with their inverses on the closed domains. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff Topology
namespace LeanShared.PeriodicChartConstants

/-- A finite family of smooth charts with compactly contained open domains and compact
marked subsets. -/
structure ChartFamily (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] where
  ι : Type
  fintype : Fintype ι
  chart : ι → OpenPartialHomeomorph M E
  mem : ∀ i, chart i ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M
  domain : ι → Set M
  isOpen_domain : ∀ i, IsOpen (domain i)
  closure_domain : ∀ i, closure (domain i) ⊆ (chart i).source
  marked : ι → Set M
  compact_marked : ∀ i, IsCompact (marked i)
  marked_domain : ∀ i, marked i ⊆ domain i

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

namespace ChartFamily

variable (F : ChartFamily E M)

/-- The compact piece of chart coordinates on which `φ_j ∘ H ∘ φ_i⁻¹` is controlled. -/
@[expose] def piece (H : M → M) (i j : F.ι) : Set E :=
  (F.chart i '' closure (F.domain i)) ∩ {y | H ((F.chart i).symm y) ∈ closure (F.domain j)}

theorem compact_image (i : F.ι) : IsCompact (F.chart i '' closure (F.domain i)) :=
  isClosed_closure.isCompact.image_of_continuousOn ((F.chart i).continuousOn.mono (F.closure_domain i))

theorem image_target (i : F.ι) : F.chart i '' closure (F.domain i) ⊆ (F.chart i).target := by
  rintro _ ⟨x, hx, rfl⟩
  exact (F.chart i).map_source (F.closure_domain i hx)

theorem compact_piece (H : M → M) (hH : Continuous H) (i j : F.ι) : IsCompact (F.piece H i j) := by
  apply (F.compact_image i).of_isClosed_subset _ inter_subset_left
  have continuous : ContinuousOn (fun y => H ((F.chart i).symm y)) (F.chart i '' closure (F.domain i)) :=
    hH.comp_continuousOn ((F.chart i).continuousOn_symm.mono (F.image_target i))
  exact continuous.preimage_isClosed_of_isClosed (F.compact_image i).isClosed isClosed_closure

theorem valid (H : M → M) (i j : F.ι) (y : E) (hy : y ∈ F.piece H i j) :
    y ∈ (F.chart i).target ∧ H ((F.chart i).symm y) ∈ (F.chart j).source :=
  ⟨F.image_target i hy.1, F.closure_domain j hy.2⟩

/-- Uniform Hölder bounds of chart representatives. -/
theorem exists_holder {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (H : M → M)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := E) (α + 1) H)
    (hH : Continuous H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i j, ∀ y ∈ F.piece H i j, ∀ z ∈ F.piece H i j,
      ‖fderiv ℝ (fun w => F.chart j (H ((F.chart i).symm w))) y -
        fderiv ℝ (fun w => F.chart j (H ((F.chart i).symm w))) z‖ ≤ C * ‖y - z‖ ^ α := by
  let := F.fintype
  have each (i j : F.ι) := regular.compact_one_holder_in_charts hα hα1 (F.chart i) (F.chart j)
    (F.mem i) (F.mem j) (F.compact_piece H hH i j) (F.valid H i j)
  choose B C hB hC _ holder using each
  refine ⟨∑ i, ∑ j, C i j, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hC i j,
    fun i j y hy z hz => ?_⟩
  refine (holder i j y hy z hz).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _))
  calc C i j ≤ ∑ j', C i j' :=
        Finset.single_le_sum (f := fun j' => C i j') (fun j' _ => hC i j') (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', C i' j' :=
        Finset.single_le_sum (f := fun i' => ∑ j', C i' j')
          (fun i' _ => Finset.sum_nonneg fun j' _ => hC i' j') (Finset.mem_univ i)

/-- Differentiability of chart representatives on the open part of the pieces. -/
theorem contDiffAt {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (H : M → M)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := E) (α + 1) H)
    (i j : F.ι) (y : E) (hy : y ∈ (F.chart i).target)
    (hHy : H ((F.chart i).symm y) ∈ (F.chart j).source) :
    ContDiffAt ℝ 1 (fun w => F.chart j (H ((F.chart i).symm w))) y :=
  (regular.one_jet_in_charts hα hα1 (F.chart i) (F.chart j) (F.mem i) (F.mem j) y hy hHy).1

end ChartFamily
end LeanShared.PeriodicChartConstants
