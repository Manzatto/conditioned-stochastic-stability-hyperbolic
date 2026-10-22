module
public import LeanShared.MeasureTheory.CoordinatePatchMeasure
public import LeanShared.MeasureTheory.WeightedJacobianTransport
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! Coordinate measures agree on chart overlaps when their densities obey
the differential Jacobian law. No measure compatibility is assumed. -/
public noncomputable section
open Set MeasureTheory Measure
open scoped ENNReal
namespace LeanShared.CoordinatePatchMeasure
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

theorem overlap (μ : Measure E) [IsAddHaarMeasure μ]
    (e d : OpenPartialHomeomorph M E) (j k : E → ℝ≥0∞) (hk : Measurable k)
    (smooth : ContDiffOn ℝ 1 (e.symm.trans d) (e.symm.trans d).source)
    (density : ∀ x ∈ (e.symm.trans d).source,
      j x = ENNReal.ofReal |(fderiv ℝ (e.symm.trans d) x).det| * k ((e.symm.trans d) x)) :
    (patch e μ j).restrict d.source = (patch d μ k).restrict e.source := by
  let A := e.symm.trans d
  let ρ := (μ.restrict A.source).withDensity j
  let ν := (μ.restrict A.target).withDensity k
  have derivatives : ∀ x ∈ A.source,
      HasFDerivWithinAt A (fderiv ℝ A x) A.source x := by
    intro x hx
    exact ((smooth x hx).contDiffAt (A.open_source.mem_nhds hx)).differentiableAt
      one_ne_zero |>.hasFDerivAt.hasFDerivWithinAt
  have weighted : ρ.map A = ν := by
    have eqDensity : ρ = (μ.restrict A.source).withDensity
        (fun x => ENNReal.ofReal |(fderiv ℝ A x).det| * k (A x)) := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem A.open_source.measurableSet] with x hx
      exact density x hx
    rw [eqDensity, WeightedJacobianTransport.map_density μ A.open_source.measurableSet
      derivatives A.injOn hk, A.image_source_eq_target]
  have measurableA : AEMeasurable A ρ := by
    apply AEMeasurable.mono_ac _ (withDensity_absolutelyContinuous _ _)
    exact A.continuousOn.aemeasurable A.open_source.measurableSet
  have measurableD : AEMeasurable d.symm (ρ.map A) := by
    rw [weighted]
    apply AEMeasurable.mono_ac _ (withDensity_absolutelyContinuous _ _)
    apply ContinuousOn.aemeasurable _ A.open_target.measurableSet
    exact d.symm.continuousOn.mono (show A.target ⊆ d.target from fun _ h => h.1)
  have mapsEqual : ρ.map e.symm = ρ.map (d.symm ∘ A) := by
    apply Measure.map_congr
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem A.open_source.measurableSet] with x hx
    exact (d.left_inv hx.2).symm
  rw [restrict_open e μ j d.open_source, restrict_open d μ k e.open_source]
  change ρ.map e.symm = ν.map d.symm
  rw [← weighted, AEMeasurable.map_map_of_aemeasurable measurableD measurableA]
  exact mapsEqual
end LeanShared.CoordinatePatchMeasure
