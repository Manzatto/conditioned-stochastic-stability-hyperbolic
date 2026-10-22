module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseChartJets
public import LeanShared.Analysis.LocalInverseDerivative
import all LeanShared.Analysis.FiniteJetComposition

/-! The constructed ORIGINAL inverse family converges in moving-point C1
jets in every fixed smooth chart pair. No inverse rate is supplied. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal
open LeanShared.FiniteJetComposition

set_option maxHeartbeats 3200000 in
theorem InverseFamily.actual_jets_in_charts
    {E M ι A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F)
    (regularity : 1 ≤ r) (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (ε : A → ℝ≥0) (controls : ∀ a, cube (ι := ι) (ε a)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ a in l, 0 < ε a)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) :
    JetConvergesOn
      (fun a => c ∘ (fun y => J.map (ε a) ((controls a).val,y)) ∘ d.symm)
      (c ∘ T.symm ∘ d.symm) l (d.target ∩ (T.symm ∘ d.symm) ⁻¹' c.source) := by
  intro z hz
  let g := c ∘ T.symm ∘ d.symm
  let f := d ∘ T ∘ c.symm
  have first : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 d.symm z :=
    (contMDiffAt_symm_of_mem_maximalAtlas (n := ∞) hd hz.1).of_le (by decide)
  have middle := inverse.contMDiffAt.comp z first
  have last : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 c (T.symm (d.symm z)) :=
    (contMDiffAt_of_mem_maximalAtlas (n := ∞) hc hz.2).of_le (by decide)
  have smooth : ContDiffAt ℝ 1 g z := (last.comp z middle).contDiffAt
  refine ⟨smooth.differentiableAt (by norm_num),fun v moving => ?_⟩
  have input := (d.continuousAt_symm hz.1).tendsto.comp moving
  have inverseMoving := J.moving_tendsto ε controls l limit positive _ _ input
  have values := (c.continuousAt hz.2).tendsto.comp inverseMoving
  obtain ⟨L,forwardDerivative,derivativeLimit⟩ := J.chart_fderiv_tendsto regularity deterministic
    (inverse.mdifferentiable (by norm_num)) ε controls l limit positive c d hc hd z hz.1 hz.2 v moving
  have identity : (f ∘ g) =ᶠ[𝓝 z] id := by
    have near := (T.symm.continuous.continuousAt.comp (d.continuousAt_symm hz.1)).preimage_mem_nhds
      (c.open_source.mem_nhds hz.2)
    filter_upwards [near,d.open_target.mem_nhds hz.1] with w hwc hwd
    change T.symm (d.symm w) ∈ c.source at hwc
    dsimp only [f,g,Function.comp_apply,id_eq]
    rw [c.left_inv hwc,T.apply_symm_apply,d.right_inv hwd]
  have inverseDerivative := LeanShared.LocalInverseDerivative.hasFDerivAt f g z L
    forwardDerivative (smooth.differentiableAt (by norm_num)) identity
  refine ⟨values,?_,?_⟩
  · have equation : fderiv ℝ (c ∘ T.symm ∘ d.symm) z = L.symm.toContinuousLinearMap := inverseDerivative.fderiv
    rw [equation]
    exact derivativeLimit
  · have window : ∀ᶠ a in l, ε a ≤ J.window :=
      (limit.eventually (gt_mem_nhds J.positive)).mono (fun _ h => h.le)
    have nearInput := moving.eventually (d.open_target.mem_nhds hz.1)
    have nearOutput := inverseMoving.eventually (c.open_source.mem_nhds hz.2)
    filter_upwards [positive,window,nearInput,nearOutput] with a hp hw hi ho
    have first : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 d.symm (v a) :=
      (contMDiffAt_symm_of_mem_maximalAtlas (n := ∞) hd hi).of_le (by decide)
    have middle := (J.map_contMDiff (ε a) hp hw (controls a)).contMDiffAt.comp (v a) first
    have last : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 c
        (J.map (ε a) ((controls a).val,d.symm (v a))) :=
      (contMDiffAt_of_mem_maximalAtlas (n := ∞) hc ho).of_le (by decide)
    exact (last.comp (v a) middle).mdifferentiableAt (by norm_num) |>.differentiableAt

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
