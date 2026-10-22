module
public import LeanShared.Geometry.FiniteSmoothReferenceDensityRegularity
public import LeanShared.Geometry.SupportedChartExtension
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! Actual reciprocal-density chart tests for distribution faithfulness.
Compact chart support proves smooth zero extension across chart boundaries. -/
public noncomputable section
open Set Filter IsManifold
open scoped Topology Manifold ContDiff SchwartzMap
namespace LeanShared.FiniteSmoothReferenceCharts.Data
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  (d : Data (E := E) (M := M))
  (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (χ : 𝓢(E, ℂ)) (compact : HasCompactSupport χ) (support : tsupport χ ⊆ c.target)

@[expose] def chartTestInverseDensity (y : E) : ℂ := χ y * ((d.localDensity c y)⁻¹ : ℝ)

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold (𝓘(ℝ,E)) ∞ M] in
private theorem inverse_density_support : tsupport (d.chartTestInverseDensity c χ) ⊆ tsupport χ :=
  tsupport_mul_subset_left

include hc support in
theorem chartTestInverseDensity_smooth : ContDiff ℝ ∞ (d.chartTestInverseDensity c χ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases inside : y ∈ c.target
  · exact (χ.smooth ⊤).contDiffAt.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp y
        ((d.localDensity_inverse_contDiffOn c hc) y inside |>.contDiffAt
          (c.open_target.mem_nhds inside)))
  · have outside : y ∉ tsupport χ := fun hy => inside (support hy)
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds outside] with z hz
    exact show d.chartTestInverseDensity c χ z = 0 from by
      simp only [chartTestInverseDensity, image_eq_zero_of_notMem_tsupport hz, zero_mul]

@[expose] def chartTestInverseWeight : M → ℂ :=
  SupportedChartExtension.function c (d.chartTestInverseDensity c χ)

include hc compact support in
theorem chartTestInverseWeight_smooth :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (d.chartTestInverseWeight c χ) :=
  SupportedChartExtension.smooth c hc (d.chartTestInverseDensity_smooth c hc χ support)
    (compact.of_isClosed_subset (isClosed_tsupport _) (d.inverse_density_support c χ))
    ((d.inverse_density_support c χ).trans support)

include compact support in
omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem chartTestInverseWeight_compact : HasCompactSupport (d.chartTestInverseWeight c χ) :=
  SupportedChartExtension.compact_support c
    (compact.of_isClosed_subset (isClosed_tsupport _) (d.inverse_density_support c χ))
    ((d.inverse_density_support c χ).trans support)

include compact support in
omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem chartTestInverseWeight_support : tsupport (d.chartTestInverseWeight c χ) ⊆ c.source := by
  apply (SupportedChartExtension.support_subset c
    (compact.of_isClosed_subset (isClosed_tsupport _) (d.inverse_density_support c χ))
    ((d.inverse_density_support c χ).trans support)).trans
  rintro _ ⟨y,hy,rfl⟩
  exact c.map_target (support (d.inverse_density_support c χ hy))

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem chartTestInverseWeight_chart (y : E) (hy : y ∈ c.target) :
    d.chartTestInverseWeight c χ (c.symm y) = χ y * ((d.localDensity c y)⁻¹ : ℝ) :=
  SupportedChartExtension.coordinate c y hy

end LeanShared.FiniteSmoothReferenceCharts.Data
