module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseJacobianWeights
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseCutoffJacobian
public import ConditionedStochasticStabilityHyperbolic.Paper.FixedCubeNoise

/-! The analytic inverse map and RAW cutoff inverse weight on the fixed
control cube are computed from the original family, with exact scalar
Jacobian duality and joint continuity on the proved positive window. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff NNReal BoundedContinuousFunction
namespace InverseFamily
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}

@[expose] def fixedInverseMap (J : InverseFamily F) (ε : ℝ≥0)
    (z : FixedControl (ι := ι)) (x : M) : M :=
  if hp : 0 < ε then J.map ε (((LeanShared.NoiseCubeRescaling.rescale (ε : ℝ) hp) z).val,x)
  else T.symm x

@[expose] def fixedJacobianWeight (J : InverseFamily F)
    (d : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M)) (w : M → ℝ)
    (ε : ℝ≥0) (p : M × FixedControl (ι := ι)) : ℝ :=
  if hp : 0 < ε then J.jacobianWeight d w 1 ε
    (p.1,(LeanShared.NoiseCubeRescaling.rescale (ε : ℝ) hp) p.2) else 0

theorem fixedInverseMap_continuous (J : InverseFamily F)
    (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ J.window) :
    Continuous (fun p : FixedControl (ι := ι) × M => J.fixedInverseMap ε p.1 p.2) := by
  have actual : Continuous (fun p : FixedControl (ι := ι) × M =>
      J.map ε (((LeanShared.NoiseCubeRescaling.rescale (ε : ℝ) hp) p.1).val,p.2)) :=
    (J.smooth ε hp hw).continuousOn.comp_continuous
      (((continuous_subtype_val.comp (LeanShared.NoiseCubeRescaling.rescale (ε : ℝ) hp).continuous).comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨J.contains ε hp hw ((LeanShared.NoiseCubeRescaling.rescale (ε : ℝ) hp) p.1).property,mem_univ _⟩)
  simpa only [fixedInverseMap,dite_eq_left hp] using actual

theorem fixedJacobianWeight_continuous
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (J : InverseFamily F) (d : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ] (w : M → ℝ) (continuousW : Continuous w)
    (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ J.window) :
    Continuous (J.fixedJacobianWeight d w ε) := by
  have actual := (J.jacobianWeight_continuous d μ w continuousW 1 ε hp hw).comp
    (f := fun p : M × FixedControl (ι := ι) =>
      (p.1,(LeanShared.NoiseCubeRescaling.rescale (ε : ℝ) hp) p.2))
    (continuous_fst.prodMk ((LeanShared.NoiseCubeRescaling.rescale (ε : ℝ) hp).continuous.comp continuous_snd))
  have same : J.fixedJacobianWeight d w ε = fun p : M × FixedControl (ι := ι) =>
      J.jacobianWeight d w 1 ε (p.1,(LeanShared.NoiseCubeRescaling.rescale (ε : ℝ) hp) p.2) := by
    funext p
    exact dite_eq_left hp
  rw [same]
  exact actual

end InverseFamily
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
