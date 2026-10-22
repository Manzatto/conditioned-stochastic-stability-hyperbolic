module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseReferenceJacobian
public import LeanShared.MeasureTheory.KilledJacobianDuality
public import Mathlib.Analysis.Normed.Group.Bounded

/-! The scalar inverse weight is computed from the actual departure weight
and actual smooth reference Jacobian. Its boundedness and killed duality are
proved, rather than supplied as inverse-density source fields. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff NNReal ENNReal
namespace InverseFamily
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}

@[expose] def jacobianWeight
    (J : InverseFamily F) (d : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (w : M → ℝ) (R : ℝ) (ε : ℝ≥0) (p : M × cube (ι := ι) ε) : ℝ := by
  classical
  exact if h : 0 < ε ∧ ε ≤ J.window then
    (max (w (J.map ε (p.2.val,p.1))) 0 / R) * d.jacobian (J.homeomorph ε h.1 h.2 p.2) p.1
  else 0

set_option maxHeartbeats 2400000 in
theorem jacobianWeight_continuous
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (J : InverseFamily F) (d : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (w : M → ℝ) (continuousW : Continuous w) (R : ℝ)
    (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ J.window) : Continuous (J.jacobianWeight d w R ε) := by
  classical
  have inverseContinuous : Continuous (fun p : M × cube (ι := ι) ε => J.map ε (p.2.val,p.1)) :=
    (J.smooth ε hp hw).continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
      (fun p => ⟨J.contains ε hp hw p.2.property,mem_univ _⟩)
  have jacobianContinuous : Continuous (fun p : M × cube (ι := ι) ε =>
      d.jacobian (J.homeomorph ε hp hw p.2) p.1) :=
    (J.referenceJacobian_continuous d μ ε hp hw).comp
      (f := fun p : M × cube (ι := ι) ε => (p.2,p.1)) continuous_swap
  have sameWeight : J.jacobianWeight d w R ε = (fun p : M × cube (ι := ι) ε =>
      (max (w (J.map ε (p.2.val,p.1))) 0 / R) * d.jacobian (J.homeomorph ε hp hw p.2) p.1) := by
    funext p
    exact dite_eq_left (And.intro hp hw)
  rw [sameWeight]
  exact (((continuousW.comp inverseContinuous).max (continuous_const (y := (0 : ℝ)))).div_const R).fun_mul jacobianContinuous

set_option maxHeartbeats 2400000 in
theorem jacobianWeight_killed_duality
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (J : InverseFamily F) (d : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (w : M → ℝ) (continuousW : Continuous w) (R : ℝ) (positiveR : 0 < R)
    (K : Set M) (measurableK : MeasurableSet K)
    (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ J.window)
    (f g : M → ℝ≥0∞) (measurableF : Measurable f) (measurableG : Measurable g)
    (a : cube (ι := ι) ε) :
    (∫⁻ x, g x * (ENNReal.ofReal (J.jacobianWeight d w R ε (x,a)) *
      K.indicator f (J.map ε (a.val,x))) ∂(d.measure μ).restrict K) =
    ∫⁻ x, f x * (ENNReal.ofReal (max (w x) 0 / R) *
      K.indicator g (F.family ε a.val x)) ∂(d.measure μ).restrict K := by
  classical
  let H := J.homeomorph ε hp hw a
  have law := d.jacobian_continuous_positive_map μ H
    (J.forward_contMDiff ε hp hw a) (J.map_contMDiff ε hp hw a)
  have actual := LeanShared.KilledJacobianDuality.lintegral (d.measure μ) H K measurableK
    (d.jacobian H) law.1.measurable law.2.2 (fun x => max (w x) 0)
    (continuousW.max continuous_const).measurable R f g measurableF measurableG
  have multiply (x : M) : ENNReal.ofReal (J.jacobianWeight d w R ε (x,a)) =
      ENNReal.ofReal (max (w (H.symm x)) 0 / R) * ENNReal.ofReal (d.jacobian H x) := by
    simp only [jacobianWeight,dite_eq_left (And.intro hp hw)]
    exact ENNReal.ofReal_mul (div_nonneg (le_max_right _ _) positiveR.le)
  simp_rw [multiply]
  exact actual

end InverseFamily
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
