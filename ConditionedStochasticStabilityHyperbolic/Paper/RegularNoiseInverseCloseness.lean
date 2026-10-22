module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseMovingWords
public import LeanShared.Topology.UniformInverseCloseness

/-! Genuine inverse convergence uses the deterministic inverse's modulus.
There is no asserted linear-in-epsilon derivative estimate. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter
open scoped Topology NNReal

theorem Maps.moving_inverse_tendsto
    {E M ι A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (ε : A → ℝ≥0) (controls : ∀ a, cube (ι := ι) (ε a)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ a in l, 0 < ε a)
    (J : A → M → M) (right : ∀ᶠ a in l, Function.RightInverse (J a) (F.family (ε a) (controls a).val))
    (v : A → M) (x : M) (moving : Tendsto v l (𝓝 x)) :
    Tendsto (fun a => J a (v a)) l (𝓝 (T.symm x)) := by
  have window : ∀ᶠ a in l, ε a ≤ F.window :=
    (limit.eventually (gt_mem_nhds F.window_positive)).mono (fun _ h => h.le)
  have realLimit : Tendsto (fun a => (ε a : ℝ)) l (𝓝 0) := by
    exact_mod_cast (NNReal.continuous_coe.continuousAt.tendsto.comp limit)
  have errorLimit : Tendsto (fun a => F.constant * (ε a : ℝ)) l (𝓝 0) := by
    simpa only [mul_zero] using realLimit.const_mul F.constant
  have distance : Tendsto (fun a => dist (v a) (T (J a (v a)))) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ errorLimit
    filter_upwards [positive,window,right] with a ha hw hr
    simpa only [hr (v a)] using F.uniform_close (ε a) ha hw (controls a) (J a (v a))
  have forward := moving.congr_dist distance
  simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using
    T.symm.continuous.continuousAt.tendsto.comp forward

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
