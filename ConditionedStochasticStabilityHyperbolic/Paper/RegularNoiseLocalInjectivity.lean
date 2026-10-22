module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformChartWords
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseDifferentiableWords
public import LeanShared.Geometry.DiffeomorphismChartDerivative
public import LeanShared.Geometry.CompactRiemannianChartBounds
public import LeanShared.Analysis.InjectivityFromDerivativeComparison

/-! Actual Whitney C1 control yields a fixed open injectivity neighborhood
of every point for all sufficiently small perturbations and all controls.
Neither local injectivity nor a local inverse is a source assumption. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal

set_option maxHeartbeats 2400000 in
theorem Maps.exists_local_injectivity_window
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm) (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ η : ℝ≥0, 0 < η ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ a : cube (ι := ι) ε,
        InjOn (F.family ε a.val) U := by
  let c := chartAt E x
  let d := chartAt E (T x)
  have hc := chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) x
  have hd := chart_mem_maximalAtlas (I := 𝓘(ℝ,E)) (n := ∞) (T x)
  have inside : x ∈ c.source := mem_chart_source E x
  have target : T x ∈ d.source := mem_chart_source E (T x)
  have smoothC := LeanShared.CompactRiemannianChartBounds.chart_differentiable c hc
  have smoothD := LeanShared.CompactRiemannianChartBounds.chart_differentiable d hd
  obtain ⟨L,derivative⟩ := LeanShared.DiffeomorphismChartDerivative.exists_equivalence T
    (deterministic.mdifferentiable one_ne_zero) inverse c d smoothC smoothD x inside target
  let g := d ∘ T ∘ c.symm
  let domain := c.target ∩ (T ∘ c.symm) ⁻¹' d.source
  have openDomain : IsOpen domain := c.isOpen_inter_preimage_symm (d.open_source.preimage T.continuous)
  have centerDomain : c x ∈ domain := ⟨c.map_source inside,by change T (c.symm (c x)) ∈ d.source; rw [c.left_inv inside]; exact target⟩
  have smoothG : ContDiffAt ℝ 1 g (c x) := by
    have first := (contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source inside)).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
    have middle : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T (c.symm (c x)) := by
      rw [c.left_inv inside]
      exact deterministic.contMDiffAt
    have last : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 d (T (c.symm (c x))) := by
      rw [c.left_inv inside]
      exact (contMDiffAt_of_mem_maximalAtlas hd target).of_le (by simp)
    exact (last.comp (c x) (middle.comp (c x) first)).contDiffAt
  let δ := 1 / (2 * (‖L.symm.toContinuousLinearMap‖ + 1))
  have denominator : 0 < 2 * (‖L.symm.toContinuousLinearMap‖ + 1) := by positivity
  have positiveδ : 0 < δ := one_div_pos.mpr denominator
  have small : ‖L.symm.toContinuousLinearMap‖ * δ < 1 := by
    dsimp only [δ]
    rw [← mul_div_assoc,mul_one]
    apply (div_lt_one denominator).mpr
    nlinarith [norm_nonneg L.symm.toContinuousLinearMap]
  have nearDerivative : ∀ᶠ y in 𝓝 (c x), ‖fderiv ℝ g y - L.toContinuousLinearMap‖ < δ / 2 := by
    have center : ‖fderiv ℝ g (c x) - L.toContinuousLinearMap‖ < δ / 2 := by
      rw [derivative.fderiv,sub_self,norm_zero]
      positivity
    exact ((smoothG.continuousAt_fderiv one_ne_zero).sub_const L.toContinuousLinearMap).norm.eventually
      (gt_mem_nhds center)
  obtain ⟨R,positiveR,valid⟩ := Metric.eventually_nhds_iff.mp (Filter.Eventually.and (openDomain.mem_nhds centerDomain) nearDerivative)
  let radius := R / 2
  have positiveRadius : 0 < radius := half_pos positiveR
  have closedValid {y : E} (hy : y ∈ Metric.closedBall (c x) radius) :
      y ∈ domain ∧ ‖fderiv ℝ g y - L.toContinuousLinearMap‖ < δ / 2 :=
    valid ((Metric.mem_closedBall.mp hy).trans_lt (half_lt_self positiveR))
  have compactBall : IsCompact (Metric.closedBall (c x) radius) := isCompact_closedBall _ _
  have domainN : Metric.closedBall (c x) radius ⊆
      c.target ∩ ((T : M → M)^[1] ∘ c.symm) ⁻¹' d.source := fun y hy => by
    simpa only [Function.iterate_one] using (closedValid hy).1
  obtain ⟨η₁,positiveη₁,jets⟩ := F.uniform_chart_word_jets regularity deterministic c d hc hd 1
    _ compactBall domainN (δ / 2) (by positivity)
  obtain ⟨η₂,positiveη₂,differentiable⟩ := F.uniformly_differentiable_chart_words regularity deterministic c d hc hd 1
    _ compactBall domainN
  let U := c.source ∩ c ⁻¹' Metric.ball (c x) radius
  refine ⟨U,c.continuousOn.isOpen_inter_preimage c.open_source Metric.isOpen_ball,
    ⟨inside,Metric.mem_ball_self positiveRadius⟩,min η₁ η₂,lt_min positiveη₁ positiveη₂,
    fun ε hp hw a => ?_⟩
  let f := d ∘ F.family ε a.val ∘ c.symm
  have localInjective : InjOn f (Metric.closedBall (c x) radius) := by
    apply LeanShared.InjectivityFromDerivativeComparison.injOn f L _ (convex_closedBall _ _) δ small
    · intro y hy
      have actual := differentiable ε hp (hw.trans (min_le_right _ _)) (fun _ => a) y hy
      exact actual
    · intro y hy
      have estimate := jets ε hp (hw.trans (min_le_left _ _)) (fun _ => a) y hy
      have noise : ‖fderiv ℝ f y - fderiv ℝ g y‖ ≤ δ / 2 := by
        exact (le_add_of_nonneg_left (norm_nonneg _)).trans estimate
      have triangle : ‖fderiv ℝ f y - L.toContinuousLinearMap‖ ≤
          ‖fderiv ℝ f y - fderiv ℝ g y‖ + ‖fderiv ℝ g y - L.toContinuousLinearMap‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le
          (fderiv ℝ f y - fderiv ℝ g y) (fderiv ℝ g y - L.toContinuousLinearMap)
      exact triangle.trans ((add_le_add noise (closedValid hy).2.le).trans_eq (add_halves δ))
  intro y hy z hz equal
  apply c.injOn hy.1 hz.1
  apply localInjective (Metric.ball_subset_closedBall hy.2) (Metric.ball_subset_closedBall hz.2)
  change d (F.family ε a.val (c.symm (c y))) = d (F.family ε a.val (c.symm (c z)))
  rw [c.left_inv hy.1,c.left_inv hz.1,equal]

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
