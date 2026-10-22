module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseNativeDerivativeBound
public import LeanShared.Geometry.BoundedRiemannianLipschitz

/-! One actual Lipschitz constant for all ORIGINAL inverse maps on one
positive noise window, for the constructed bounded length metric. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Bundle IsManifold
open scoped Topology Manifold ContDiff Bundle NNReal

theorem InverseFamily.uniform_native_lipschitz
    {E M ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (hr : 1 ≤ r)
    (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm) :
    ∃ η : ℝ≥0, 0 < η ∧ η ≤ J.window ∧ ∃ L : ℝ≥0,
      ∀ (ε : ℝ≥0) (_hp : 0 < ε) (_hw : ε ≤ η) (_hwJ : ε ≤ J.window) (control : cube (ι := ι) ε),
      let g := fun z => J.map ε (control.val,z)
      let _ : MetricSpace M := LeanShared.BoundedRiemannianMetric.metric (E := E)
      LipschitzWith L g := by
  obtain ⟨η,hη,window,B,hB,bound⟩ := J.uniform_native_derivative_bound hr regular inverse
  let B₀ : ℝ≥0 := ⟨B,hB.le⟩
  refine ⟨η,hη,window,max B₀ 1,?_⟩
  intro ε hp hw hwJ control
  exact LeanShared.BoundedRiemannianMetric.lipschitz_of_derivative_bound
    (fun z => J.map ε (control.val,z)) (J.map_contMDiff ε hp hwJ control)
    B₀ (by exact_mod_cast hB) (bound ε hp hw control)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
