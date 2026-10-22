module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseReferenceJacobian
public import ConditionedStochasticStabilityHyperbolic.Spectral.ComputedCutoffJacobian

/-! The literal per-control RAW cutoff adjoint identity is proved for the
original noise family and the constructed smooth reference. It is independent
of a chosen completed test space; every genuine function is covered. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff NNReal BoundedContinuousFunction

set_option maxHeartbeats 1600000 in
theorem InverseFamily.cutoff_jacobian
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (d : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (K : Set M) (measurableK : MeasurableSet K) (w : M → ℝ) (support : Function.support w ⊆ K)
    (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ J.window) (a : cube (ι := ι) ε)
    (f : K →ᵇ ℂ) (g : M → ℂ) :
    (∫ x : K, ActualCutoffAdjoint.raw K
      (fun p : M × cube (ι := ι) ε => F.family ε p.2.val p.1)
      (fun y => w y.val) a f x * g x.val ∂(d.measure μ).comap Subtype.val) =
      ∫ y : K, f y * (((d.jacobian (J.homeomorph ε hp hw a) y.val *
        w (J.map ε (a.val,y.val)) : ℝ) : ℂ) * g (J.map ε (a.val,y.val)))
        ∂(d.measure μ).comap Subtype.val := by
  have law := d.jacobian_continuous_positive_map μ (J.homeomorph ε hp hw a)
    (J.forward_contMDiff ε hp hw a) (J.map_contMDiff ε hp hw a)
  exact ActualCutoffAdjoint.jacobian_from_pushforward (d.measure μ) K measurableK
    (J.homeomorph ε hp hw a) _ a (fun _ => rfl) _ law.1.measurable
    (fun x => (law.2.1 x).le) law.2.2 w support f g

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
