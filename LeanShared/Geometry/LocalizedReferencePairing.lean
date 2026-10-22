module
public import LeanShared.Geometry.ConstructedManifoldLocalization
public import LeanShared.Geometry.ReferenceDensityChartTestWeight
public import LeanShared.Geometry.ReferenceDensityChartIntegral
public import LeanShared.Geometry.FiniteSmoothReferenceMeasure
public import LeanShared.Geometry.NativeChartTest

/-! The reference-measure pairing of a localized core function with a
continuous function on the manifold is the sum, over the localization charts,
of the Euclidean pairings of the literal local coordinates with the chart
readings of the function weighted by `χ_i · ρ_i` (`χ_i = 1` on the local support,
`ρ_i` the reference density). -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff SchwartzMap
namespace LeanShared.LocalizedReferencePairing
open ConstructedManifoldLocalization FiniteSmoothReferenceCharts

variable {E M J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  (e : J → OpenPartialHomeomorph M E) {S : Set M} (D : ConstructedManifoldLocalization.Data e S)
  (he : ∀ j, e j ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
  {Core : Type*} [AddCommGroup Core] [Module ℂ Core]
  (functions : Core →ₗ[ℂ] (M → ℂ))
  (smooth : ∀ f : Core, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (functions f))
  (d : FiniteSmoothReferenceCharts.Data (E := E) (M := M)) (μ : Measure E) [μ.IsAddHaarMeasure]
  (χ : D.indices → 𝓢(E, ℂ))
  (χ_one : ∀ i, ∀ y ∈ ConstructedManifoldLocalization.support e D i, χ i y = 1)

/-- The chart weight `χ_i ρ_i`. -/
@[expose] def weight (i : D.indices) : E → ℂ := d.chartTestDensity (e i) (χ i)

theorem localize_zero_outside (i : D.indices) (f : Core) {y : E}
    (hy : y ∉ ConstructedManifoldLocalization.support e D i) :
    (localize e D he functions smooth i f).val y = 0 :=
  (localize e D he functions smooth i f).property y hy

include χ_one in
theorem chart_term (i : D.indices) (f : Core) (g : M → ℂ) (y : E) (hy : y ∈ (e i).target) :
    (d.localDensity (e i) y : ℂ) * (D.cutoff i ((e i).symm y) * functions f ((e i).symm y) *
      g ((e i).symm y)) =
      (localize e D he functions smooth i f).val y *
        NativeChartTest.reading (e i) (weight e D d χ i) g y := by
  rw [NativeChartTest.reading_of_mem (e i) _ g hy]
  have hloc : (localize e D he functions smooth i f).val y =
      D.cutoff i ((e i).symm y) * functions f ((e i).symm y) := by
    have := localize_apply e D he functions smooth i f ((e i).symm y) ((e i).map_target hy)
    rwa [(e i).right_inv hy] at this
  by_cases hs : y ∈ ConstructedManifoldLocalization.support e D i
  · rw [hloc]
    change _ = D.cutoff i ((e i).symm y) * functions f ((e i).symm y) *
      (χ i y * (d.localDensity (e i) y : ℂ) * g ((e i).symm y))
    rw [χ_one i y hs]
    ring
  · rw [localize_zero_outside e D he functions smooth i f hs, zero_mul]
    rw [localize_zero_outside e D he functions smooth i f hs] at hloc
    rw [← hloc, zero_mul, mul_zero]


theorem continuous_integrable {ν : Measure M} [IsFiniteMeasure ν] {h : M → ℂ} (hh : Continuous h) :
    Integrable h ν :=
  hh.integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (subset_univ _))

include χ_one in
/-- The reference pairing is the sum of the chart pairings. -/
theorem integral_decomposition (f : Core) (vanish : ∀ x, x ∉ S → functions f x = 0)
    (g : M → ℂ) (hg : Continuous g) :
    (∫ x, functions f x * g x ∂d.measure μ) =
      ∑ i, ∫ y, (localize e D he functions smooth i f).val y *
        NativeChartTest.reading (e i) (weight e D d χ i) g y ∂μ := by
  have hf : Continuous (functions f) := (smooth f).continuous
  have hcut : ∀ i, Continuous (D.cutoff i) := fun i => (D.smooth i).continuous
  have split : ∀ x, functions f x * g x = ∑ i, D.cutoff i x * functions f x * g x := by
    intro x
    by_cases hx : x ∈ S
    · rw [← Finset.sum_mul, ← Finset.sum_mul, D.partition x hx, one_mul]
    · simp only [vanish x hx, mul_zero, zero_mul, Finset.sum_const_zero]
  calc (∫ x, functions f x * g x ∂d.measure μ)
      = ∫ x, ∑ i, D.cutoff i x * functions f x * g x ∂d.measure μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => split x
    _ = ∑ i, ∫ x, D.cutoff i x * functions f x * g x ∂d.measure μ :=
        integral_finsetSum _ (fun i _ => continuous_integrable (((hcut i).mul hf).mul hg))
    _ = ∑ i, ∫ y, (localize e D he functions smooth i f).val y *
          NativeChartTest.reading (e i) (weight e D d χ i) g y ∂μ := by
        apply Finset.sum_congr rfl
        intro i _
        have source : (∫ x, D.cutoff i x * functions f x * g x ∂d.measure μ) =
            ∫ x in (e i).source, D.cutoff i x * functions f x * g x ∂d.measure μ := by
          symm
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro x hx
          have : x ∉ tsupport (D.cutoff i) := fun h => hx (D.support i h)
          rw [image_eq_zero_of_notMem_tsupport this, zero_mul, zero_mul]
        have chart := d.integral_chart μ (e i) (he i)
          (fun x => D.cutoff i x * functions f x * g x) (((hcut i).mul hf).mul hg)
        have target : (∫ y in (e i).target, (d.localDensity (e i) y : ℂ) *
            (D.cutoff i ((e i).symm y) * functions f ((e i).symm y) * g ((e i).symm y)) ∂μ) =
            ∫ y in (e i).target, (localize e D he functions smooth i f).val y *
              NativeChartTest.reading (e i) (weight e D d χ i) g y ∂μ :=
          setIntegral_congr_fun (e i).open_target.measurableSet fun y hy =>
            chart_term e D he functions smooth d χ χ_one i f g y hy
        have whole : (∫ y in (e i).target, (localize e D he functions smooth i f).val y *
              NativeChartTest.reading (e i) (weight e D d χ i) g y ∂μ) =
            ∫ y, (localize e D he functions smooth i f).val y *
              NativeChartTest.reading (e i) (weight e D d χ i) g y ∂μ := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro y hy
          have hs : y ∉ ConstructedManifoldLocalization.support e D i := fun h =>
            hy (ChartLocalization.localSupport_subset_target (e i) (D.cutoff i) (D.support i) h)
          rw [localize_zero_outside e D he functions smooth i f hs, zero_mul]
        rw [source, chart]
        exact target.trans whole

end LeanShared.LocalizedReferencePairing
