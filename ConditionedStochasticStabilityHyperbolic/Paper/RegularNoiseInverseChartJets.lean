module
public import ConditionedStochasticStabilityHyperbolic.Paper.ConstructedInverseNoiseFamily
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseArbitraryWordCharts
public import LeanShared.Geometry.DiffeomorphismChartDerivative
public import LeanShared.Analysis.InverseDerivativeConvergence
import all LeanShared.Analysis.FiniteJetComposition

/-! Actual inverse chart derivatives converge with no imposed rate in the
original noise scale. The inverse derivative is obtained from the proved
inverse identity and continuity of Banach-algebra inversion. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal
open LeanShared.FiniteJetComposition

set_option maxHeartbeats 3200000 in
theorem InverseFamily.chart_fderiv_tendsto
    {E M ι A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F)
    (regularity : 1 ≤ r) (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (ε : A → ℝ≥0) (controls : ∀ a, cube (ι := ι) (ε a)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ a in l, 0 < ε a)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (z : E) (inside : z ∈ d.target) (target : T.symm (d.symm z) ∈ c.source)
    (v : A → E) (moving : Tendsto v l (𝓝 z)) :
    ∃ L : E ≃L[ℝ] E,
      HasFDerivAt (d ∘ T ∘ c.symm) L.toContinuousLinearMap (c (T.symm (d.symm z))) ∧
      Tendsto (fun a => fderiv ℝ
        (c ∘ (fun x => J.map (ε a) ((controls a).val,x)) ∘ d.symm) (v a)) l
        (𝓝 L.symm.toContinuousLinearMap) := by
  let x := T.symm (d.symm z)
  let f := fun a => d ∘ F.family (ε a) (controls a).val ∘ c.symm
  let g := fun a => c ∘ (fun y => J.map (ε a) ((controls a).val,y)) ∘ d.symm
  have targetForward : T x ∈ d.source := by
    simpa only [x,Homeomorph.apply_symm_apply] using d.map_target inside
  obtain ⟨L,derivative⟩ := LeanShared.DiffeomorphismChartDerivative.exists_equivalence T
    (deterministic.mdifferentiable (by norm_num)) inverse c d
    ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by norm_num),
      (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by norm_num)⟩
    ⟨(contMDiffOn_of_mem_maximalAtlas hd).mdifferentiableOn (by norm_num),
      (contMDiffOn_symm_of_mem_maximalAtlas hd).mdifferentiableOn (by norm_num)⟩ x target targetForward
  refine ⟨L,derivative,?_⟩
  have input := (d.continuousAt_symm inside).tendsto.comp moving
  have inverseMoving := J.moving_tendsto ε controls l limit positive _ _ input
  have gMoving : Tendsto (fun a => g a (v a)) l (𝓝 (c x)) :=
    (c.continuousAt target).tendsto.comp inverseMoving
  have jets := F.actual_word_jets_in_charts regularity deterministic ε (fun _ => controls)
    l limit positive c d hc hd 1
  have forwardJets := (jets (c x) ⟨c.map_source target,?_⟩).2 _ gMoving
  · have raw := forwardJets.2.1
    have jetLimit : Tendsto (fun a => fderiv ℝ (f a) (g a (v a))) l
        (𝓝 L.toContinuousLinearMap) := by
      simpa only [LeanShared.FiniteJetComposition.word,Function.comp_def,Function.iterate_one,
        Function.iterate_zero,Function.comp_id,Function.id_comp,id_eq] using
        (derivative.fderiv ▸ raw)
    have window : ∀ᶠ a in l, ε a ≤ J.window :=
      (limit.eventually (gt_mem_nhds J.positive)).mono (fun _ h => h.le)
    have nearInput := moving.eventually (d.open_target.mem_nhds inside)
    have nearOutput := inverseMoving.eventually (c.open_source.mem_nhds target)
    have inverseDifferentiable : ∀ᶠ a in l, DifferentiableAt ℝ (g a) (v a) := by
      filter_upwards [positive,window,nearInput,nearOutput] with a hp hw hi ho
      have first : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 d.symm (v a) :=
        (contMDiffAt_symm_of_mem_maximalAtlas (n := ∞) hd hi).of_le (by decide)
      have middle := (J.map_contMDiff (ε a) hp hw (controls a)).contMDiffAt.comp (v a) first
      have last : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 c
          (J.map (ε a) ((controls a).val,d.symm (v a))) :=
        (contMDiffAt_of_mem_maximalAtlas (n := ∞) hc ho).of_le (by decide)
      exact (last.comp (v a) middle).mdifferentiableAt (by norm_num) |>.differentiableAt
    have identities : ∀ᶠ a in l, (f a ∘ g a) =ᶠ[𝓝 (v a)] id := by
      filter_upwards [positive,window,nearInput,nearOutput] with a hp hw hi ho
      have inverseContinuous := (J.map_contMDiff (ε a) hp hw (controls a)).continuous
      have near := (inverseContinuous.continuousAt.comp (d.continuousAt_symm hi)).preimage_mem_nhds
        (c.open_source.mem_nhds ho)
      filter_upwards [near,d.open_target.mem_nhds hi] with w hwc hwd
      change J.map (ε a) ((controls a).val,d.symm w) ∈ c.source at hwc
      dsimp only [f,g,Function.comp_apply,id_eq]
      rw [c.left_inv hwc,J.right (ε a) hp hw _ (J.contains (ε a) hp hw (controls a).property),d.right_inv hwd]
    have forwardDifferentiable : ∀ᶠ a in l, DifferentiableAt ℝ (f a) (g a (v a)) := by
      simpa only [f,LeanShared.FiniteJetComposition.word,Function.comp_def,Function.iterate_one,
        Function.iterate_zero,Function.comp_id,Function.id_comp,id_eq] using forwardJets.2.2
    exact LeanShared.InverseDerivativeConvergence.fderiv_tendsto f g v l L jetLimit
      forwardDifferentiable inverseDifferentiable identities
  · change T (c.symm (c x)) ∈ d.source
    rw [c.left_inv target]
    exact targetForward

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
