module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformChartWords
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseDifferentiableWords
public import LeanShared.Geometry.DiffeomorphismChartDerivative
public import LeanShared.Geometry.CompactRiemannianChartBounds
public import LeanShared.Analysis.SurjectivityFromDerivativeComparison
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseWordTarget

/-! Actual Whitney jets and the quantitative Banach inverse theorem give a
fixed neighborhood of each deterministic image contained in every small
perturbation image. This includes zero-dimensional manifold models. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal

set_option maxHeartbeats 2400000 in
theorem Maps.exists_local_surjectivity_window
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm) (x : M) :
    ∃ W : Set M, IsOpen W ∧ T x ∈ W ∧ ∃ η : ℝ≥0, 0 < η ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ a : cube (ι := ι) ε,
        W ⊆ range (F.family ε a.val) := by
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
  let jetError := min (δ / 2) (δ * radius / 4)
  have positiveJetError : 0 < jetError := lt_min (by positivity) (by positivity)
  obtain ⟨η₁,positiveη₁,jets⟩ := F.uniform_chart_word_jets regularity deterministic c d hc hd 1
    _ compactBall domainN jetError positiveJetError
  obtain ⟨η₂,positiveη₂,differentiable⟩ := F.uniformly_differentiable_chart_words regularity deterministic c d hc hd 1
    _ compactBall domainN
  have sourceBall : Metric.closedBall (c x) radius ⊆ c.target := fun y hy => (closedValid hy).1.1
  have compactSource : IsCompact (c.symm '' Metric.closedBall (c x) radius) :=
    compactBall.image_of_continuousOn (c.symm.continuousOn.mono sourceBall)
  have targetSource : MapsTo (T : M → M) (c.symm '' Metric.closedBall (c x) radius) d.source := by
    rintro y ⟨z,hz,rfl⟩
    exact (closedValid hz).1.2
  obtain ⟨η₃,positiveη₃,outputs⟩ := F.exists_uniform_word_target 1 _ d.source compactSource d.open_source
    (by simpa only [Function.iterate_one] using targetSource)
  let W := d.source ∩ d ⁻¹' Metric.ball (d (T x)) (δ * radius / 2)
  refine ⟨W,d.continuousOn.isOpen_inter_preimage d.open_source Metric.isOpen_ball,
    ⟨target,Metric.mem_ball_self (by positivity)⟩,
    min η₁ (min η₂ η₃),lt_min positiveη₁ (lt_min positiveη₂ positiveη₃),
    fun ε hp hw a y hy => ?_⟩
  let f := d ∘ F.family ε a.val ∘ c.symm
  have comparison (z : E) (hz : z ∈ Metric.closedBall (c x) radius) :
      ‖fderiv ℝ f z - L.toContinuousLinearMap‖ ≤ δ := by
    have estimate := jets ε hp (hw.trans (min_le_left _ _)) (fun _ => a) z hz
    have noise : ‖fderiv ℝ f z - fderiv ℝ g z‖ ≤ δ / 2 :=
      ((le_add_of_nonneg_left (norm_nonneg _)).trans estimate).trans (min_le_left _ _)
    have triangle : ‖fderiv ℝ f z - L.toContinuousLinearMap‖ ≤
        ‖fderiv ℝ f z - fderiv ℝ g z‖ + ‖fderiv ℝ g z - L.toContinuousLinearMap‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le
        (fderiv ℝ f z - fderiv ℝ g z) (fderiv ℝ g z - L.toContinuousLinearMap)
    exact triangle.trans ((add_le_add noise (closedValid hz).2.le).trans_eq (add_halves δ))
  have onto := LeanShared.SurjectivityFromDerivativeComparison.surjOn_closedBall f L (c x) radius
    positiveRadius.le ⟨δ,positiveδ.le⟩
    (fun z hz => differentiable ε hp (hw.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (fun _ => a) z hz) comparison
  have slope : (‖L.symm.toContinuousLinearMap‖ + 1)⁻¹ - δ = δ := by
    dsimp only [δ]
    rw [inv_eq_one_div]
    field_simp
    ring
  change SurjOn f (Metric.closedBall (c x) radius)
    (Metric.closedBall (f (c x)) (((‖L.symm.toContinuousLinearMap‖ + 1)⁻¹ - δ) * radius)) at onto
  rw [slope] at onto
  have centerEstimate := jets ε hp (hw.trans (min_le_left _ _)) (fun _ => a) (c x)
    (Metric.mem_closedBall_self positiveRadius.le)
  have closeCenter : dist (d (T x)) (f (c x)) ≤ δ * radius / 4 := by
    have estimate : ‖f (c x) - g (c x)‖ ≤ δ * radius / 4 :=
      ((le_add_of_nonneg_right (norm_nonneg _)).trans centerEstimate).trans (min_le_right _ _)
    have centerG : g (c x) = d (T x) := by
      change d (T (c.symm (c x))) = d (T x)
      rw [c.left_inv inside]
    rw [centerG] at estimate
    simpa only [dist_eq_norm,norm_sub_rev] using estimate
  have targetBall : d y ∈ Metric.closedBall (f (c x)) (δ * radius) := by
    apply Metric.mem_closedBall.mpr
    have near : dist (d y) (d (T x)) < δ * radius / 2 := hy.2
    have triangle := dist_triangle (d y) (d (T x)) (f (c x))
    nlinarith [mul_pos positiveδ positiveRadius]
  obtain ⟨z,hz,equal⟩ := onto targetBall
  refine ⟨c.symm z,?_⟩
  have output : F.family ε a.val (c.symm z) ∈ d.source := outputs ε hp
    (hw.trans ((min_le_right _ _).trans (min_le_right _ _))) (fun _ => a) (mem_image_of_mem _ hz)
  exact d.injOn output hy.1 equal

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
