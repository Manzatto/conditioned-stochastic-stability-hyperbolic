module
public import LeanShared.MeasureTheory.WeightedJacobianTransport
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! The inverse Jacobian density of a genuine local C1 diffeomorphism is
constructed from its actual derivative. No density transformation equation
is assumed. -/
public noncomputable section
namespace LeanShared.InverseJacobianPushforward
open Set MeasureTheory Measure
open scoped ENNReal

theorem map_density
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
    (e : OpenPartialHomeomorph E E)
    (inverse : ContDiffOn ℝ 1 e.symm e.target)
    (p : E → ℝ≥0∞) (measurable : Measurable p) :
    ((μ.restrict e.source).withDensity p).map e =
      (μ.restrict e.target).withDensity
        (fun y => ENNReal.ofReal |(fderiv ℝ e.symm y).det| * p (e.symm y)) := by
  let ν := (μ.restrict e.target).withDensity
    (fun y => ENNReal.ofReal |(fderiv ℝ e.symm y).det| * p (e.symm y))
  have derivatives : ∀ y ∈ e.target,
      HasFDerivWithinAt e.symm (fderiv ℝ e.symm y) e.target y := by
    intro y hy
    exact ((inverse y hy).contDiffAt (e.open_target.mem_nhds hy)).differentiableAt one_ne_zero
      |>.hasFDerivAt.hasFDerivWithinAt
  have inverseLaw : ν.map e.symm = (μ.restrict e.source).withDensity p := by
    have raw := WeightedJacobianTransport.map_density μ e.open_target.measurableSet derivatives e.symm.injOn measurable
    rw [show e.symm '' e.target = e.source from e.symm.image_source_eq_target] at raw
    exact raw
  have measurableInverse : AEMeasurable e.symm ν :=
    (e.symm.continuousOn.aemeasurable e.open_target.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have measurableForward : AEMeasurable e (ν.map e.symm) := by
    rw [inverseLaw]
    exact (e.continuousOn.aemeasurable e.open_source.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [←inverseLaw, AEMeasurable.map_map_of_aemeasurable measurableForward measurableInverse]
  have eq : e ∘ e.symm =ᵐ[ν] id := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
    exact e.right_inv hy
  rw [Measure.map_congr eq,Measure.map_id]

end LeanShared.InverseJacobianPushforward
