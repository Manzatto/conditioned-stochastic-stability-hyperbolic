module
public import LeanShared.Analysis.ImmersionPullbackJacobian
public import LeanShared.MeasureTheory.WeightedJacobianTransport

/-! Change of leaf parameters is derived from actual derivatives and the
Euclidean Jacobian theorem. This identifies the nonlinear image measure,
without assuming a leaf change-of-variables law. -/
public noncomputable section
open Set Filter MeasureTheory Measure
open scoped ENNReal
namespace LeanShared.ParametrizedImmersionTransport
variable {U E : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem map_tangent_density (μ : Measure U) [IsAddHaarMeasure μ]
    (h : OpenPartialHomeomorph U U) (γS γT : U → E) (F : E → E)
    (sourceRegular : ContDiffOn ℝ 1 γS h.source)
    (targetRegular : ContDiffOn ℝ 1 γT h.target)
    (coordinateRegular : ContDiffOn ℝ 1 h h.source)
    (forwardRegular : ∀ x ∈ h.source, DifferentiableAt ℝ F (γS x))
    (agrees : ∀ x ∈ h.source, F (γS x) = γT (h x)) :
    ((μ.restrict h.source).withDensity (fun x =>
      ENNReal.ofReal (((fderiv ℝ F (γS x)).toLinearMap.domRestrict
        (fderiv ℝ γS x).toLinearMap.range).normDet) *
      IntrinsicCoordinatePatchMeasures.density γS h.source x)).map (F ∘ γS) =
    ((μ.restrict h.target).withDensity
      (IntrinsicCoordinatePatchMeasures.density γT h.target)).map γT := by
  let j : U → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (((fderiv ℝ F (γS x)).toLinearMap.domRestrict
      (fderiv ℝ γS x).toLinearMap.range).normDet) *
    IntrinsicCoordinatePatchMeasures.density γS h.source x
  let k := IntrinsicCoordinatePatchMeasures.density γT h.target
  let ρ := (μ.restrict h.source).withDensity j
  let ν := (μ.restrict h.target).withDensity k
  have derivatives : ∀ x ∈ h.source, HasFDerivWithinAt h (fderiv ℝ h x) h.source x := by
    intro x hx
    exact ((coordinateRegular.differentiableOn one_ne_zero) x hx).differentiableAt
      (h.open_source.mem_nhds hx) |>.hasFDerivAt.hasFDerivWithinAt
  have density : ∀ x ∈ h.source,
      j x = ENNReal.ofReal |(fderiv ℝ h x).det| * k (h x) := by
    intro x hx
    have sourceDiff := ((sourceRegular.differentiableOn one_ne_zero) x hx).differentiableAt
      (h.open_source.mem_nhds hx)
    have chain := ImmersionPullbackJacobian.chain sourceDiff.hasFDerivAt
      (forwardRegular x hx).hasFDerivAt
    have change := IntrinsicCoordinateJacobian.coordinate_change h
      (coordinateRegular.differentiableOn one_ne_zero)
      (targetRegular.differentiableOn one_ne_zero) (p := F ∘ γS) (q := γT) agrees hx
    dsimp only [j, k]
    simp only [IntrinsicCoordinatePatchMeasures.density, indicator_of_mem hx,
      indicator_of_mem (h.map_source hx)]
    rw [← ENNReal.ofReal_mul (LinearMap.normDet_nonneg _), ← chain, change,
      ENNReal.ofReal_mul (LinearMap.normDet_nonneg _), mul_comm]
  have weighted : ρ.map h = ν := by
    have eqDensity : ρ = (μ.restrict h.source).withDensity
        (fun x => ENNReal.ofReal |(fderiv ℝ h x).det| * k (h x)) := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem h.open_source.measurableSet] with x hx
      exact density x hx
    rw [eqDensity, WeightedJacobianTransport.map_density μ h.open_source.measurableSet
      derivatives h.injOn (IntrinsicCoordinatePatchMeasures.measurable_density targetRegular h.open_target),
      h.image_source_eq_target]
  have measurableH : AEMeasurable h ρ := by
    exact (h.continuousOn.aemeasurable h.open_source.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have measurableTarget : AEMeasurable γT (ρ.map h) := by
    rw [weighted]
    exact (targetRegular.continuousOn.aemeasurable h.open_target.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have same : ρ.map (F ∘ γS) = ρ.map (γT ∘ h) := by
    apply Measure.map_congr
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem h.open_source.measurableSet] with x hx
    exact agrees x hx
  change ρ.map (F ∘ γS) = ν.map γT
  rw [← weighted, AEMeasurable.map_map_of_aemeasurable measurableTarget measurableH]
  exact same
end LeanShared.ParametrizedImmersionTransport
