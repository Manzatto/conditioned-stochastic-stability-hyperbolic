module
public import LeanShared.Geometry.ReferenceInverseDensityChartTest
public import LeanShared.Analysis.SchwartzJetKernel

/-! A supported manifold chart cutoff and any Schwartz test construct the
actual smooth reciprocal-density global test which isolates that chart's
local distribution. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff SchwartzMap
namespace LeanShared.FiniteSmoothReferenceCharts.Data
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  (d : Data (E:=E) (M:=M))
  (c : OpenPartialHomeomorph M E) (hc : c∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (θ : M→ℂ) (smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
  (compact : HasCompactSupport θ) (support : tsupport θ⊆c.source)

@[expose] def isolationCoordinate (φ : 𝓢(E,ℂ)) : 𝓢(E,ℂ) :=
  ((ChartLocalization.coordinate_hasCompactSupport c θ support compact (fun _=>1)).mul_right
    (f':=(φ:E→ℂ))).toSchwartzMap
    ((ChartLocalization.coordinate_contDiff c θ support hc smooth compact (fun _=>1) contMDiff_const).mul
      (φ.smooth ⊤))

include support in
omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem isolationCoordinate_compact (φ : 𝓢(E,ℂ)) :
    HasCompactSupport (isolationCoordinate c hc θ smooth compact support φ) :=
  (ChartLocalization.coordinate_hasCompactSupport c θ support compact (fun _=>1)).mul_right

include support in
omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem isolationCoordinate_support (φ : 𝓢(E,ℂ)) :
    tsupport (isolationCoordinate c hc θ smooth compact support φ)⊆c.target := by
  have first : tsupport (ChartLocalization.coordinate c θ (fun _=>1))⊆
      ChartLocalization.localSupport c θ := by
    apply closure_minimal
    · intro y hy
      by_contra outside
      exact hy (ChartLocalization.coordinate_zero_outside c θ (fun _=>1) y outside)
    · exact (ChartLocalization.localSupport_isCompact c θ support compact).isClosed
  exact tsupport_mul_subset_left.trans (first.trans (ChartLocalization.localSupport_subset_target c θ support))

@[expose] def isolationTest (φ : 𝓢(E,ℂ)) : M→ℂ :=
  d.chartTestInverseWeight c (isolationCoordinate c hc θ smooth compact support φ)

include hc smooth compact support in
theorem isolationTest_smooth (φ : 𝓢(E,ℂ)) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ (d.isolationTest c hc θ smooth compact support φ) :=
  d.chartTestInverseWeight_smooth c hc _
    (isolationCoordinate_compact c hc θ smooth compact support φ)
    (isolationCoordinate_support c hc θ smooth compact support φ)

include hc in
omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold (𝓘(ℝ,E)) ∞ M] in
theorem isolationTest_formula (φ : 𝓢(E,ℂ)) (x : M) (inside : x∈c.source) :
    d.isolationTest c hc θ smooth compact support φ x=
      θ x*φ (c x)*((d.localDensity c (c x))⁻¹:ℝ) := by
  have actual := d.chartTestInverseWeight_chart c
    (isolationCoordinate c hc θ smooth compact support φ) (c x) (c.map_source inside)
  rw [c.left_inv inside] at actual
  exact actual.trans (by
    change (ChartLocalization.coordinate c θ (fun _=>1) (c x)*φ (c x))*_= _
    simp only [ChartLocalization.coordinate,ite_eq_left (c.map_source inside),c.left_inv inside,mul_one])
end LeanShared.FiniteSmoothReferenceCharts.Data
