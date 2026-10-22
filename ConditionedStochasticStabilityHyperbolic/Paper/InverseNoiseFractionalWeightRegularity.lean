module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseFractionalGlobalWeightHolder
public import LeanShared.Geometry.BoundedRiemannianHolderRegularity

/-! Literal fractional chart regularity of the computed inverse weight.
The original weight may have regularity below one. The scale/control
window is constructed from the actual original regular-noise family. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle MeasureTheory Measure
open scoped Topology Manifold ContDiff Bundle NNReal

set_option maxHeartbeats 2400000 in
theorem InverseFamily.jacobianWeight_fractional_regular
    {E M ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MetricSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {r a : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (s : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (ha : 0 < a) (ha1 : a < 1) (lower : a+1 < r)
    (regular : LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (w : M → ℝ) (q : ℝ) (lowerW : a < q)
    (regularW : LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q w)
    (R : ℝ) (hR : 0 < R) :
    ∃ η : ℝ≥0, 0 < η ∧ η ≤ J.window ∧
      ∀ (ε : ℝ≥0), 0 < ε → ε ≤ η → ∀ control : cube (ι := ι) ε,
        LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := ℂ) a
          (fun x => (J.jacobianWeight s w R ε (x,control) : ℂ)) := by
  obtain ⟨η,hη,window,B,C,_hB,hC,bound⟩ :=
    J.jacobianWeight_fractional_global_holder s μ ha ha1 lower regular inverse w q lowerW regularW R hR
  refine ⟨η,hη,window,fun ε hp hw control => ?_⟩
  have continuous : Continuous (fun x => J.jacobianWeight s w R ε (x,control)) :=
    (J.jacobianWeight_continuous s μ w
    regularW.differentiable.continuous R ε hp (hw.trans window)).comp
      (continuous_id.prodMk continuous_const)
  apply LeanShared.BoundedRiemannianMetric.regular_of_native_holder ha ha1
    (Complex.continuous_ofReal.comp continuous) hC
  dsimp only
  intro x y
  simpa only [Function.comp_apply,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using
    (bound ε hp hw control).2 x y

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
