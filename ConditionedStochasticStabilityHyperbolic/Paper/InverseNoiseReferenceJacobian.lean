module
public import ConditionedStochasticStabilityHyperbolic.Paper.ConstructedInverseNoiseFamily
public import LeanShared.Geometry.FiniteSmoothReferenceParametricJacobian

/-! Computed reference Jacobians for the ORIGINAL small-noise family.
The inverse family is already constructed from literal regular noise.
Joint control/state continuity gives bounds before any driving law is chosen. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff NNReal

namespace InverseFamily
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}

theorem forward_contMDiff (J : InverseFamily F) (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ J.window)
    (a : cube (ι := ι) ε) : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (F.family ε a.val) := by
  obtain ⟨O,_,contains,smooth⟩ := F.joint_C1 ε hp (hw.trans J.window_le)
  exact smooth.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
    (fun _ => ⟨contains a.property,mem_univ _⟩)

@[expose] def homeomorph (J : InverseFamily F) (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ J.window)
    (a : cube (ι := ι) ε) : M ≃ₜ M where
  toFun := F.family ε a.val
  invFun := fun x => J.map ε (a.val,x)
  left_inv := J.left ε hp hw a.val (J.contains ε hp hw a.property)
  right_inv := J.right ε hp hw a.val (J.contains ε hp hw a.property)
  continuous_toFun := (J.forward_contMDiff ε hp hw a).continuous
  continuous_invFun := (J.map_contMDiff ε hp hw a).continuous

set_option maxHeartbeats 2400000 in
theorem referenceJacobian_continuous
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (J : InverseFamily F) (d : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ J.window) :
    Continuous (fun q : cube (ι := ι) ε × M => d.jacobian (J.homeomorph ε hp hw q.1) q.2) := by
  exact d.parametricJacobian_continuous μ Subtype.val continuous_subtype_val
    (J.homeomorph ε hp hw) (J.forward_contMDiff ε hp hw) (J.map_contMDiff ε hp hw)
    (J.map ε) (J.domain ε) (J.open_domain ε)
    (fun a => J.contains ε hp hw a.property) (J.smooth ε hp hw) (fun _ _ => rfl)

end InverseFamily
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
