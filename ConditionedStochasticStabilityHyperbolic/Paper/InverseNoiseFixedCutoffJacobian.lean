module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseFixedJacobian

/-! The exact analytic cutoff Jacobian source on fixed controls is proved
for the ORIGINAL maps and the computed inverse action. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff NNReal BoundedContinuousFunction

set_option maxHeartbeats 1600000 in
theorem InverseFamily.fixed_cutoff_jacobian
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (d : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (K : Set M) (measurableK : MeasurableSet K)
    (w : M → ℝ) (support : Function.support w ⊆ K) (nonnegative : ∀ x, 0 ≤ w x)
    (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ J.window) (z : FixedControl (ι := ι))
    (f : K →ᵇ ℂ) (g : M → ℂ) :
    (∫ x : K, ActualCutoffAdjoint.raw K (fun p : M × FixedControl (ι := ι) => F.fixedMap ε p.1 p.2)
      (fun y => w y.val) z f x * g x.val ∂(d.measure μ).comap Subtype.val) =
      ∫ y : K, f y * ((J.fixedJacobianWeight d w ε (y.val,z) : ℂ) *
        g (J.fixedInverseMap ε z y.val)) ∂(d.measure μ).comap Subtype.val := by
  let a := (LeanShared.NoiseCubeRescaling.rescale (ε : ℝ) hp) z
  have actual := J.cutoff_jacobian d μ K measurableK w support ε hp hw a f g
  have weight (y : M) : J.fixedJacobianWeight d w ε (y,z) =
      d.jacobian (J.homeomorph ε hp hw a) y * w (J.map ε (a.val,y)) := by
    simp only [InverseFamily.fixedJacobianWeight, dite_eq_left hp, InverseFamily.jacobianWeight,
      dite_eq_left (And.intro hp hw),max_eq_left (nonnegative _),div_one]
    exact mul_comm _ _
  simpa only [ActualCutoffAdjoint.raw,Maps.fixedMap,dite_eq_left hp,InverseFamily.fixedInverseMap,weight] using actual

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
