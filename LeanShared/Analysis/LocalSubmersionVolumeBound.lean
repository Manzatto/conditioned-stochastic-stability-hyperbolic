module
public import LeanShared.Analysis.SubmersionAugmentedVolume
public import LeanShared.Analysis.HaarLinearCoordinates
public import LeanShared.Analysis.BoundedFiberProjection

/-! A C1 full-rank map of finite-dimensional real spaces pushes forward local
source volume to a measure bounded by target volume, including excess control
dimensions. All inverse coordinates, constants, and fiber bounds are derived. -/
public noncomputable section
namespace LeanShared.SubmersionLinearCoordinates
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem exists_local_submersion_volume_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure E) (σ : Measure F) [μ.IsAddHaarMeasure] [σ.IsAddHaarMeasure]
    {f : E → F} {x : E} (smooth : ContDiffAt ℝ 1 f x)
    (rank : Function.Surjective (fderiv ℝ f x)) :
    ∃ s : Set E, IsOpen s ∧ x ∈ s ∧ DifferentiableOn ℝ f s ∧
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ (μ.restrict s).map f ≤ C • σ := by
  obtain ⟨P, e, coordinates, u, openU, xu, diffG, C, finiteC, boundG⟩ :=
    exists_augmented_local_volume_bound μ smooth rank
  let g : E → E := fun z => e.symm (P z, f z)
  let H : E → (fderiv ℝ f x).ker × F := fun z => (P z, f z)
  let κ : Measure (fderiv ℝ f x).ker := Measure.addHaar
  obtain ⟨c, finitec, haar⟩ :=
    HaarLinearCoordinates.exists_finite_factor e μ (κ.prod σ)
  have fnear : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f z :=
    (smooth.eventually (by decide)).mono (fun _ h => h.differentiableAt one_ne_zero)
  obtain ⟨v, vsub, openV, xv⟩ := mem_nhds_iff.mp fnear
  let s := u ∩ v ∩ Metric.ball x 1
  have openS : IsOpen s := (openU.inter openV).inter Metric.isOpen_ball
  have xs : x ∈ s := ⟨⟨xu, xv⟩, Metric.mem_ball_self zero_lt_one⟩
  have diffF : DifferentiableOn ℝ f s :=
    fun z hz => (vsub hz.1.2).differentiableWithinAt
  have gAE : AEMeasurable g (μ.restrict u) :=
    diffG.continuousOn.aemeasurable₀ openU.measurableSet.nullMeasurableSet
  have HAE : AEMeasurable H (μ.restrict s) :=
    (P.continuous.continuousOn.prodMk diffF.continuousOn).aemeasurable₀
      openS.measurableSet.nullMeasurableSet
  have gAES : AEMeasurable g (μ.restrict s) :=
    gAE.mono_measure (Measure.restrict_mono_set μ (fun _ hz => hz.1.1))
  have joint : (μ.restrict s).map H ≤ (C * c) • κ.prod σ := by
    have smaller := Measure.map_mono_of_aemeasurable
      (Measure.restrict_mono_set μ (show s ⊆ u from fun _ hz => hz.1.1)) gAE
    have mapped := Measure.map_mono (smaller.trans boundG) e.continuous.measurable
    rw [Measure.map_smul C e.continuous.measurable.aemeasurable, haar, smul_smul,
      AEMeasurable.map_map_of_aemeasurable e.continuous.measurable.aemeasurable gAES] at mapped
    simpa only [g, H, Function.comp_def, e.apply_symm_apply] using mapped
  let B := Metric.closedBall (0 : (fderiv ℝ f x).ker) (‖P‖ * (‖x‖ + 1))
  have finiteB : κ B ≠ ∞ := (isCompact_closedBall _ _).measure_lt_top.ne
  have supported : ∀ᵐ z ∂(μ.restrict s).map H, z.1 ∈ B := by
    apply (ae_map_iff HAE ((Metric.isClosed_closedBall : IsClosed B).measurableSet.preimage
      measurable_fst)).2
    filter_upwards [ae_restrict_mem openS.measurableSet] with z hz
    change P z ∈ Metric.closedBall 0 (‖P‖ * (‖x‖ + 1))
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (P.le_opNorm z).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have near : ‖z - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hz.2
    exact (norm_le_norm_sub_add z x).trans
      (by simpa only [add_comm] using add_le_add_left near.le ‖x‖)
  have marginal := BoundedFiberProjection.map_snd_le κ σ ((μ.restrict s).map H)
    (C * c) B joint supported
  rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable HAE] at marginal
  refine ⟨s, openS, xs, diffF, C * c * κ B, ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top finiteC finitec) finiteB
  · exact marginal

end LeanShared.SubmersionLinearCoordinates
