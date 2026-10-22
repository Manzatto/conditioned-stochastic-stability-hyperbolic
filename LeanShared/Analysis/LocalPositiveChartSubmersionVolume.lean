module
public import LeanShared.Analysis.UniformChartSubmersionVolume
public import LeanShared.Analysis.ControlRankNeighborhood

/-! C1 and full control rank at one chart point construct actual open
state/control patches with a uniform volume bound for the manifold endpoint.
All radii, compact neighborhoods, and domination constants are produced. -/
public noncomputable section
namespace LeanShared.SubmersionLinearCoordinates
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem exists_local_positive_chart_bound
    {X A E M : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (μ : Measure X) (ρ : Measure A) (ν : Measure E) (σ : Measure M)
    [μ.IsAddHaarMeasure] [ρ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (e : OpenPartialHomeomorph M E) (r : E → ℝ)
    (patchBound : CoordinatePatchMeasure.patch e ν (fun y => ENNReal.ofReal (r y)) ≤ σ)
    (continuousR : ContinuousOn r e.target)
    {f : X × A → E} {x : X} {a : A}
    (smooth : ContDiffAt ℝ 1 f (x, a))
    (rank : Function.Surjective (fderiv ℝ (fun b => f (x, b)) a))
    (target : f (x, a) ∈ e.target) (positivePoint : 0 < r (f (x, a))) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ y ∈ Metric.ball x ε, ∀ B : Set M, MeasurableSet B →
        ρ ((fun b => e.symm (f (y, b))) ⁻¹' B ∩ Metric.ball a ε) ≤ C * σ B := by
  obtain ⟨O, openO, memberO, smoothO, rankO⟩ := exists_control_rank_neighborhood smooth rank
  have positiveNear : {y | 0 < r y} ∈ 𝓝 (f (x, a)) :=
    ((continuousR (f (x, a)) target).continuousAt (e.open_target.mem_nhds target)).eventually
      (Ioi_mem_nhds positivePoint)
  obtain ⟨δ, positiveδ, targetBall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (e.open_target.mem_nhds target) positiveNear)
  have targetContained := targetBall.trans inter_subset_left
  let patch := CoordinatePatchMeasure.patch e ν (fun y => ENNReal.ofReal (r y))
  have near : O ∩ f ⁻¹' Metric.ball (f (x, a)) δ ∈ 𝓝 (x, a) :=
    inter_mem (openO.mem_nhds memberO)
      (smooth.continuousAt (Metric.ball_mem_nhds _ positiveδ))
  obtain ⟨ε, positiveε, contained⟩ := Metric.nhds_basis_closedBall.mem_iff.mp near
  have rectangle : Metric.closedBall x ε ×ˢ Metric.closedBall a ε ⊆
      Metric.closedBall (x, a) ε := by rw [closedBall_prod_same]
  have containedO := rectangle.trans (contained.trans inter_subset_left)
  have image (y : X) (hy : y ∈ Metric.closedBall x ε)
      (b : A) (hb : b ∈ Metric.closedBall a ε) : f (y, b) ∈ Metric.closedBall (f (x, a)) δ :=
    Metric.ball_subset_closedBall ((contained (rectangle ⟨hy, hb⟩)).2)
  obtain ⟨C, finiteC, bound⟩ := exists_uniform_chart_bound μ ρ ν patch e r
    (CoordinatePatchMeasure.restrict_source e ν (fun y => ENNReal.ofReal (r y)))
    (isCompact_closedBall x ε) (isCompact_closedBall a ε) (isCompact_closedBall (f (x, a)) δ)
    targetContained (continuousR.mono targetContained) (fun y hy => (targetBall hy).2)
    openO containedO smoothO (fun y hy b hb => rankO (y, b) (containedO ⟨hy, hb⟩)) image
  refine ⟨ε, positiveε, C, finiteC, ?_⟩
  intro y hy B measurableB
  have inside : y ∈ interior (Metric.closedBall x ε) :=
    (Metric.isOpen_ball.subset_interior_iff.mpr Metric.ball_subset_closedBall) hy
  have continuousF : ContinuousOn (fun b => f (y, b)) (Metric.closedBall a ε) := by
    intro b hb
    exact (((smoothO (y, b) (containedO ⟨Metric.ball_subset_closedBall hy, hb⟩)).contDiffAt
      (openO.mem_nhds (containedO ⟨Metric.ball_subset_closedBall hy, hb⟩))).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have continuousRaw : ContinuousOn (fun b => e.symm (f (y, b))) (Metric.closedBall a ε) :=
    e.symm.continuousOn.comp continuousF
      (fun b hb => targetContained (image y (Metric.ball_subset_closedBall hy) b hb))
  have measurableRaw : AEMeasurable (fun b => e.symm (f (y, b)))
      (ρ.restrict (Metric.closedBall a ε)) :=
    continuousRaw.aemeasurable₀ Metric.isClosed_closedBall.measurableSet.nullMeasurableSet
  calc
    ρ ((fun b => e.symm (f (y, b))) ⁻¹' B ∩ Metric.ball a ε) ≤
        ρ ((fun b => e.symm (f (y, b))) ⁻¹' B ∩ Metric.closedBall a ε) :=
      measure_mono (inter_subset_inter_right _ Metric.ball_subset_closedBall)
    _ = ((ρ.restrict (Metric.closedBall a ε)).map (fun b => e.symm (f (y, b)))) B := by
      rw [Measure.map_apply_of_aemeasurable measurableRaw measurableB,
        Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet]
    _ ≤ C * patch B := bound y inside B
    _ ≤ C * σ B := by gcongr

end LeanShared.SubmersionLinearCoordinates
