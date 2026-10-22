module
public import LeanShared.Analysis.CompactLocalParametricSubmersionVolume
public import LeanShared.MeasureTheory.CoordinatePatchVolumeBound

/-! Actual positive-density target charts turn the proved uniform Euclidean
submersion estimate into a local manifold-volume estimate. -/
public noncomputable section
namespace LeanShared.SubmersionLinearCoordinates
open Set MeasureTheory
open scoped ENNReal Topology

theorem exists_uniform_chart_bound
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
    (reference : σ.restrict e.source =
      CoordinatePatchMeasure.patch e ν (fun x => ENNReal.ofReal (r x)))
    {K : Set X} {L : Set A} {J : Set E}
    (compactK : IsCompact K) (compactL : IsCompact L) (compactJ : IsCompact J)
    (containedJ : J ⊆ e.target) (continuousR : ContinuousOn r J) (positiveR : ∀ y ∈ J, 0 < r y)
    {f : X × A → E} {O : Set (X × A)}
    (openO : IsOpen O) (contained : K ×ˢ L ⊆ O) (smooth : ContDiffOn ℝ 1 f O)
    (rank : ∀ x ∈ K, ∀ a ∈ L, Function.Surjective (fderiv ℝ (fun b => f (x, b)) a))
    (image : ∀ x ∈ K, ∀ a ∈ L, f (x, a) ∈ J) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x ∈ interior K,
      (ρ.restrict L).map (fun a => e.symm (f (x, a))) ≤ C • σ := by
  obtain ⟨C, finiteC, euclidean⟩ := exists_uniform_volume_bound_of_neighborhood
    μ ρ ν compactK compactL openO contained smooth rank
  obtain ⟨D, finiteD, inverseBound⟩ := CoordinatePatchMeasure.exists_inverse_compact_volume_bound
    e ν σ r compactJ containedJ continuousR positiveR reference
  refine ⟨C * D, ENNReal.mul_ne_top finiteC finiteD, ?_⟩
  intro x hx
  have continuousF : ContinuousOn (fun a => f (x, a)) L := by
    intro a ha
    exact (((smooth (x, a) (contained ⟨interior_subset hx, ha⟩)).contDiffAt
      (openO.mem_nhds (contained ⟨interior_subset hx, ha⟩))).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have measurableF : AEMeasurable (fun a => f (x, a)) (ρ.restrict L) :=
    continuousF.aemeasurable₀ compactL.measurableSet.nullMeasurableSet
  let pushed := (ρ.restrict L).map (fun a => f (x, a))
  have supported : pushed.restrict J = pushed := by
    apply Measure.restrict_eq_self_of_ae_mem
    apply (ae_map_iff measurableF compactJ.measurableSet).mpr
    filter_upwards [ae_restrict_mem compactL.measurableSet] with a ha
    exact image x (interior_subset hx) a ha
  have bound : pushed ≤ C • ν.restrict J := by
    have h := Measure.restrict_mono_measure (euclidean x hx) J
    rw [supported, Measure.restrict_smul] at h
    exact h
  have inverseAE : AEMeasurable e.symm (ν.restrict J) :=
    (e.symm.continuousOn.mono containedJ).aemeasurable₀ compactJ.measurableSet.nullMeasurableSet
  have inversePushed : AEMeasurable e.symm pushed :=
    (inverseAE.smul_measure C).mono_measure bound
  have mapped := Measure.map_mono_of_aemeasurable bound (inverseAE.smul_measure C)
  rw [Measure.map_smul C inverseAE,
    AEMeasurable.map_map_of_aemeasurable inversePushed measurableF] at mapped
  exact mapped.trans (by simpa only [smul_smul] using smul_le_smul_left C inverseBound)

end LeanShared.SubmersionLinearCoordinates
