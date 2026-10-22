module

public import LeanShared.Geometry.SmoothFractionalRegularity

/-! Smooth maps between boundaryless smooth manifolds satisfy the literal
real-indexed fractional chart regularity at every nonnegative finite
order. The target need not be a normed vector space. -/

@[expose] public noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity
variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem regular_map_of_smooth {f : M → N}
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f) {r : ℝ} (hr : 0 ≤ r) :
    Regular (E := E) (F := F) r f := by
  refine ⟨hr, hf.of_le (by simp), ?_⟩
  intro _ x
  have hc : ContDiffAt ℝ ∞ (chartMap (E := E) (F := F) f x)
      (extChartAt (𝓘(ℝ, E)) x x) := by
    have h := (contMDiffAt_iff.mp (hf.contMDiffAt (x := x))).2
    simpa only [chartMap, ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] using h
  have hd : ContDiffAt ℝ 1
      (iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E := E) (F := F) f x))
      (extChartAt (𝓘(ℝ, E)) x x) := hc.iteratedFDeriv_right (by simp)
  have target : f ⁻¹' (extChartAt (𝓘(ℝ, F)) (f x)).source ∈ 𝓝 x :=
    hf.continuous.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (f x)).mem_nhds (mem_extChartAt_source (f x)))
  have back : (extChartAt (𝓘(ℝ, E)) x).symm ⁻¹'
      (f ⁻¹' (extChartAt (𝓘(ℝ, F)) (f x)).source) ∈ 𝓝 (extChartAt (𝓘(ℝ, E)) x x) := by
    apply (continuousAt_extChartAt_symm (I := 𝓘(ℝ, E)) x).preimage_mem_nhds
    simpa only [extChartAt_to_inv] using target
  have domain : chartDomain (E := E) (F := F) f x ∈ 𝓝 (extChartAt (𝓘(ℝ, E)) x x) :=
    inter_mem ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)) back
  have fraction_le : r - (⌊r⌋₊ : ℝ) ≤ 1 := by
    linarith [Nat.lt_floor_add_one r]
  exact LocalSmoothHolder.exists_holder_on hd fraction_le domain

end LeanShared.FractionalManifoldRegularity
