module
public import LeanShared.Geometry.FractionalManifoldRegularity
public import LeanShared.Analysis.LocalSmoothHolder
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! Smooth manifold functions have every finite real regularity order.
The fractional condition is proved on the actual chart derivative from its
local C¹ regularity, without rounding a fractional order up in an assumption. -/
public noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]

/-- A smooth function into a normed space satisfies the literal local
fractional chart definition at every nonnegative real order. -/
theorem regular_of_smooth {f : M → F}
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f) {u : ℝ} (hu : 0 ≤ u) :
    Regular (E := E) (F := F) u f := by
  refine ⟨hu, hf.of_le (by simp), ?_⟩
  intro _ x
  have hc : ContDiffAt ℝ ∞ (chartMap (E := E) (F := F) f x)
      (extChartAt (𝓘(ℝ, E)) x x) := by
    have h := (contMDiffAt_iff.mp (hf.contMDiffAt (x := x))).2
    simpa only [chartMap, ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] using h
  have hd : ContDiffAt ℝ 1
      (iteratedFDeriv ℝ ⌊u⌋₊ (chartMap (E := E) (F := F) f x))
      (extChartAt (𝓘(ℝ, E)) x x) := hc.iteratedFDeriv_right (by simp)
  have domain_eq : chartDomain (E := E) (F := F) f x =
      (extChartAt (𝓘(ℝ, E)) x).target := by
    simp [chartDomain, chartAt_self_eq]
  have domain_nhds : chartDomain (E := E) (F := F) f x ∈
      𝓝 (extChartAt (𝓘(ℝ, E)) x x) := by
    rw [domain_eq]
    exact (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  have fraction_le : u - (⌊u⌋₊ : ℝ) ≤ 1 := by
    linarith [Nat.lt_floor_add_one u]
  exact LocalSmoothHolder.exists_holder_on hd fraction_le domain_nhds
end LeanShared.FractionalManifoldRegularity
