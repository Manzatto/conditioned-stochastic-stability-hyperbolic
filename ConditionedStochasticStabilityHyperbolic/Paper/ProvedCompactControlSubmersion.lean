module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedEndpointOpenness
public import ConditionedStochasticStabilityHyperbolic.Paper.ControlSubmersionSources
public import LeanShared.Geometry.FiniteSmoothReferenceSubmersionVolume
public import LeanShared.Geometry.FiniteSmoothReferenceSupport
public import LeanShared.MeasureTheory.SubtypePushforward
public import LeanShared.Probability.SignedRandomMapUniformSmoothing

/-! All ordinary control-submersion consequences are proved for a constructed
finite smooth reference on a compact manifold: endpoint openness, uniform
volume domination, and smoothing of bounded measurable observables. -/
public noncomputable section
open Set MeasureTheory Filter Function IsManifold
open scoped Manifold ContDiff Topology ENNReal NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise

theorem cubeVolume_isFinite
    {ι : Type*} [Fintype ι] (ε : ℝ≥0) : IsFiniteMeasure (cubeVolume (ι := ι) ε) := by
  have compact := LeanShared.NoiseCubeRescaling.cube_compact (ι := ι) (ε : ℝ)
  constructor
  rw [cubeVolume, (MeasurableEmbedding.subtype_coe compact.measurableSet).comap_apply]
  simpa only [Set.image_univ, Subtype.range_coe] using
    (compact.measure_lt_top (μ := (volume : Measure (Control (ι := ι)))))

theorem finite_reference_volume_bound
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
    [Fintype ι] [MeasurableSpace M] [BorelSpace M] [MeasurableSpace E] [BorelSpace E]
    (d : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (ν : Measure E) [ν.IsAddHaarMeasure]
    (ε : ℝ≥0) (H : Control (ι := ι) × M → M)
    (smooth : ∃ O : Set (Control (ι := ι)), IsOpen O ∧
      (LeanShared.NoiseCubeRescaling.cube (ι := ι) ε : Set (Control (ι := ι))) ⊆ O ∧
      ContMDiffOn ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) 1 H (O ×ˢ univ))
    (rank : ∀ (a : cube (ι := ι) ε) (x : M),
      Surjective (mfderiv (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E))
        (fun b : Control (ι := ι) => H (b, x)) a.val)) :
    ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∀ x,
      (cubeVolume (ι := ι) ε).map (fun a => H (a.val, x)) ≤ C • d.measure ν := by
  obtain ⟨O, openO, contained, smoothH⟩ := smooth
  let swapped := fun z : M × Control (ι := ι) => H (z.2, z.1)
  have swappedSmooth : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, Control (ι := ι))))
      (𝓘(ℝ, E)) 1 swapped (univ ×ˢ O) :=
    smoothH.comp (contMDiffOn_snd.prodMk contMDiffOn_fst) (fun _ hz => ⟨hz.2, hz.1⟩)
  have compact := LeanShared.NoiseCubeRescaling.cube_compact (ι := ι) (ε : ℝ)
  obtain ⟨C, finiteC, bound⟩ := d.uniform_submersion_volume_bound
    (volume : Measure (Control (ι := ι))) ν compact openO contained swappedSmooth
      (fun x a ha => rank ⟨a, ha⟩ x)
  refine ⟨C, finiteC, ?_⟩
  intro x
  have continuousH : ContinuousOn (fun a : Control (ι := ι) => H (a, x))
      (LeanShared.NoiseCubeRescaling.cube (ι := ι) ε) :=
    smoothH.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ ha => ⟨contained ha, mem_univ _⟩)
  rw [show (cubeVolume (ι := ι) ε).map (fun a => H (a.val, x)) =
      ((volume : Measure (Control (ι := ι))).restrict
        (LeanShared.NoiseCubeRescaling.cube (ι := ι) ε)).map (fun a => H (a, x)) from
    LeanShared.SubtypePushforward.map_comap_comp volume compact.measurableSet
      (continuousH.aemeasurable₀ compact.measurableSet.nullMeasurableSet)]
  exact bound x

theorem controlSubmersionSources_of_finite_reference
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
    [Fintype ι] [MeasurableSpace M] [BorelSpace M] [MeasurableSpace E] [BorelSpace E]
    (d : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (ν : Measure E) [ν.IsAddHaarMeasure] :
    ControlSubmersionSources (E := E) (ι := ι) (d.measure ν) := by
  refine ⟨?_, proved_openCubeEndpointContract, ?_⟩
  · intro ε _positiveε H smooth rank g _compactG smoothG f measurableF boundedF
    obtain ⟨O, openO, contained, smoothH⟩ := smooth
    obtain ⟨C, finiteC, bound⟩ := finite_reference_volume_bound d ν ε H
      ⟨O, openO, contained, smoothH⟩ rank
    have : IsFiniteMeasure (cubeVolume (ι := ι) ε) := cubeVolume_isFinite ε
    let gCube : cube (ι := ι) ε →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
      ⟨fun a => g a.val, smoothG.continuous.comp continuous_subtype_val⟩
    have controlContinuous (x : M) : Continuous (fun a : cube (ι := ι) ε => H (a.val, x)) :=
      smoothH.continuousOn.comp_continuous (continuous_subtype_val.prodMk continuous_const)
        (fun a => ⟨contained a.property, mem_univ _⟩)
    have stateContinuous (a : cube (ι := ι) ε) : Continuous (fun x : M => H (a.val, x)) :=
      smoothH.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        (fun _ => ⟨contained a.property, mem_univ _⟩)
    obtain ⟨B, _nonnegativeB, boundF⟩ := boundedF
    have integrableF : Integrable f (d.measure ν) :=
      Integrable.of_bound measurableF.aestronglyMeasurable B (ae_of_all _ boundF)
    have normalizedBound (x : M) : (cubeVolume (ι := ι) ε).map (fun a => H (a.val, x)) ≤
        ((C.toNNReal : ℝ≥0) : ℝ≥0∞) • d.measure ν := by
      rw [ENNReal.coe_toNNReal finiteC]
      exact bound x
    exact LeanShared.StrongFellerFromUniformDomination.continuous_weighted_random_integral
      (cubeVolume (ι := ι) ε) (d.measure ν) (fun x a => H (a.val, x))
      (fun x => (controlContinuous x).measurable.aemeasurable) stateContinuous
      C.toNNReal normalizedBound (fun a => g a.val) gCube.continuous.measurable
      ‖gCube‖₊ (fun a => gCube.norm_coe_le_norm a) integrableF
  · intro ε _positiveε H smooth rank
    exact finite_reference_volume_bound d ν ε H smooth rank

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
