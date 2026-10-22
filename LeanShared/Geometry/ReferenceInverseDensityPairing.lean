module
public import LeanShared.Geometry.ReferenceInverseDensityIsolationTest
public import LeanShared.Geometry.ReferenceDensityChartIntegral

/-! The constructed reciprocal-density global test exactly recovers a local
Schwartz pairing against the literal chart coordinate. -/
public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff SchwartzMap
namespace LeanShared.FiniteSmoothReferenceCharts.Data
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

set_option maxHeartbeats 800000 in
theorem isolation_pairing (d : Data (E:=E) (M:=M))
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (c : OpenPartialHomeomorph M E) (hc : c∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (θ : M→ℂ) (smooth : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
    (compact : HasCompactSupport θ) (support : tsupport θ⊆c.source)
    (φ : 𝓢(E,ℂ)) (f : M→ℂ) (continuousF : Continuous f) :
    ∫ x,f x*d.isolationTest c hc θ smooth compact support φ x ∂d.measure μ=
      ∫ y,ChartLocalization.coordinate c θ f y*φ y ∂μ := by
  classical
  calc
    _ = ∫ x in c.source,f x*d.isolationTest c hc θ smooth compact support φ x ∂d.measure μ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      change f x*SupportedChartExtension.function c _ x=0
      simp only [SupportedChartExtension.function,ite_eq_right hx,mul_zero]
    _ = ∫ y in c.target,(d.localDensity c y:ℂ)*
        (f (c.symm y)*d.isolationTest c hc θ smooth compact support φ (c.symm y)) ∂μ :=
      d.integral_chart μ c hc _ (continuousF.mul
        (d.isolationTest_smooth c hc θ smooth compact support φ).continuous)
    _ = ∫ y in c.target,ChartLocalization.coordinate c θ f y*φ y ∂μ := by
      apply setIntegral_congr_fun c.open_target.measurableSet
      intro y hy
      dsimp only
      rw [d.isolationTest_formula c hc θ smooth compact support φ (c.symm y) (c.map_target hy),
        c.right_inv hy]
      have inverse : (d.localDensity c y:ℂ)*((d.localDensity c y)⁻¹:ℝ)=1 := by
        rw [←Complex.ofReal_mul,mul_inv_cancel₀ (d.localDensity_positive c hc y hy).ne',Complex.ofReal_one]
      simp only [ChartLocalization.coordinate,ite_eq_left hy]
      calc
        _ = ((d.localDensity c y:ℂ)*((d.localDensity c y)⁻¹:ℝ))*
          ((θ (c.symm y)*f (c.symm y))*φ y) := by ring
        _ = _ := by rw [inverse,one_mul]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      simp only [ChartLocalization.coordinate,ite_eq_right hy,zero_mul]
end LeanShared.FiniteSmoothReferenceCharts.Data
