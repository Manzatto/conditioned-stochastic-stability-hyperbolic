module
public import LeanShared.MeasureTheory.CoordinatePatchCompatibility
public import LeanShared.Analysis.IntrinsicCoordinateJacobian

/-! Canonical coordinate densities of an immersion. Their compatibility on
overlaps is proved from differentiation and rectangular Jacobians. -/
public noncomputable section
open Set Filter MeasureTheory Measure
open scoped Topology ENNReal
namespace LeanShared.IntrinsicCoordinatePatchMeasures
variable {U E M : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

@[expose] def density (p : U → E) (s : Set U) : U → ℝ≥0∞ :=
  s.indicator (fun x => ENNReal.ofReal (fderiv ℝ p x).toLinearMap.normDet)

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] in
theorem measurable_density {p : U → E} {s : Set U}
    (smooth : ContDiffOn ℝ 1 p s) (hs : IsOpen s) : Measurable (density p s) := by
  classical
  exact (ENNReal.continuous_ofReal.comp_continuousOn
    (IntrinsicCoordinateJacobian.continuousOn_jacobian smooth hs)).measurable_piecewise
    continuousOn_const hs.measurableSet

theorem compatible (μ : Measure U) [IsAddHaarMeasure μ]
    (e d : OpenPartialHomeomorph M U) (ι : M → E)
    (transition : ContDiffOn ℝ 1 (e.symm.trans d) (e.symm.trans d).source)
    (parametrization : ContDiffOn ℝ 1 (ι ∘ d.symm) d.target) :
    (CoordinatePatchMeasure.patch e μ (density (ι ∘ e.symm) e.target)).restrict d.source =
      (CoordinatePatchMeasure.patch d μ (density (ι ∘ d.symm) d.target)).restrict e.source := by
  apply CoordinatePatchMeasure.overlap μ e d _ _
    (measurable_density parametrization d.open_target) transition
  intro x hx
  let A := e.symm.trans d
  have source : x ∈ e.target := hx.1
  have target : A x ∈ d.target := (A.map_source hx).1
  have change := IntrinsicCoordinateJacobian.coordinate_change A
    (transition.differentiableOn one_ne_zero)
    ((parametrization.differentiableOn one_ne_zero).mono
      (show A.target ⊆ d.target from fun _ h => h.1))
    (p := ι ∘ e.symm) (q := ι ∘ d.symm)
    (fun y hy => by
      change ι (e.symm y) = ι (d.symm (d (e.symm y)))
      have hd : e.symm y ∈ d.source := hy.2
      exact congrArg ι (d.left_inv hd).symm) hx
  change density (ι ∘ e.symm) e.target x =
    ENNReal.ofReal |(fderiv ℝ A x).det| * density (ι ∘ d.symm) d.target (A x)
  simp only [density, indicator_of_mem source, indicator_of_mem target]
  rw [change, ENNReal.ofReal_mul (LinearMap.normDet_nonneg _), mul_comm]
end LeanShared.IntrinsicCoordinatePatchMeasures
