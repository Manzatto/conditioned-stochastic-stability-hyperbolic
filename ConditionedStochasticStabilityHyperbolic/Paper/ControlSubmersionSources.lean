module

public import ConditionedStochasticStabilityHyperbolic.Paper.SmoothSubmersionSource
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedNoiseDensityBound
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoisePlaqueCover
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseControlNondegeneracy

/-! One law-independent ordinary rank-chart source supplies scalar smoothing,
endpoint openness and uniform cube-volume domination. No spectral or
conditional-measure conclusion is a field. Reference-volume positivity is
separate, so closed live boundaries need not have full reference support. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Function IsManifold
open scoped Manifold ContDiff Topology NNReal ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M]

/-- Ordinary finite-dimensional rank-chart consequences for a fixed smooth
volume reference. Validity for that reference is a classical volume input. -/
structure ControlSubmersionSources (σ : Measure M) : Prop where
  smooth_density : SmoothCubeSubmersionContract (E := E) (M := M) (ι := ι)
  open_image : OpenCubeEndpointContract (E := E) (M := M) (ι := ι)
  volume_domination : ∀ ε : ℝ≥0, 0 < ε → ∀ H : Control (ι := ι) × M → M,
    (∃ O : Set (Control (ι := ι)), IsOpen O ∧
      (LeanShared.NoiseCubeRescaling.cube (ι := ι) ε : Set (Control (ι := ι))) ⊆ O ∧
      ContMDiffOn ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) 1 H (O ×ˢ univ)) →
    (∀ (a : cube (ι := ι) ε) (x : M),
      Surjective (mfderiv (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E))
        (fun b : Control (ι := ι) => H (b, x)) a.val)) →
    ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∀ x,
      (cubeVolume (ι := ι) ε).map (fun a => H (a.val, x)) ≤ C • σ

variable {T : M ≃ₜ M} {r : ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace M] in
theorem Maps.volume_bound_from_submersion
    (F : Maps (E := E) (ι := ι) T r) (σ : Measure M)
    (source : ControlSubmersionSources (E := E) (ι := ι) σ)
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ F.window) :
    ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∀ x,
      (cubeVolume (ι := ι) ε).map (fun a => F.family ε a.val x) ≤ C • σ :=
  source.volume_domination ε hε (fun z => F.family ε z.1 z.2)
    (F.joint_C1 ε hε hw) (F.control_surjective ε hε hw)

omit [FiniteDimensional ℝ E] [BorelSpace M] in
theorem Maps.inverse_volume_bound_from_submersion
    (F : Maps (E := E) (ι := ι) T r) (σ : Measure M)
    (source : ControlSubmersionSources (E := E) (ι := ι) σ)
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ F.window)
    (G : Control (ι := ι) × M → M)
    (joint : ∃ O : Set (Control (ι := ι)), IsOpen O ∧
      (LeanShared.NoiseCubeRescaling.cube (ι := ι) ε : Set (Control (ι := ι))) ⊆ O ∧
      ContMDiffOn ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) 1 G (O ×ˢ univ))
    (identity : ∀ (a : cube (ι := ι) ε) (y : M),
      ∀ᶠ z in 𝓝 a.val, F.family ε z (G (z, y)) = y)
    (spatial : ∀ (a : cube (ι := ι) ε) (y : M),
      Injective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
        (F.family ε a.val) (G (a.val, y)))) :
    ∃ C : ℝ≥0∞, C ≠ (∞ : ℝ≥0∞) ∧ ∀ x,
      (cubeVolume (ι := ι) ε).map (fun a => G (a.val, x)) ≤ C • σ := by
  have rank : ∀ (a : cube (ι := ι) ε) (y : M),
      Surjective (mfderiv (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E))
        (fun b : Control (ι := ι) => G (b, y)) a.val) := by
    intro a y
    obtain ⟨O, hO, hcube, smooth⟩ := joint
    have hat : ContMDiffAt ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E)))
        (𝓘(ℝ, E)) 1 G (a.val, y) := smooth.contMDiffAt
      ((hO.prod isOpen_univ).mem_nhds ⟨hcube a.property, mem_univ y⟩)
    have hp : ContMDiffAt (𝓘(ℝ, Control (ι := ι)))
        ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) 1
        (fun p : Control (ι := ι) => (p, y)) a.val := contMDiffAt_id.prodMk contMDiffAt_const
    exact F.inverse_control_surjective ε hε hw G a y
      ((hat.comp a.val hp).mdifferentiableAt one_ne_zero) (identity a y) (spatial a y)
  exact source.volume_domination ε hε G joint rank

omit [FiniteDimensional ℝ E] [BorelSpace M] in
theorem Maps.inverse_transition_ac_from_submersion
    (F : Maps (E := E) (ι := ι) T r) (σ : Measure M)
    (source : ControlSubmersionSources (E := E) (ι := ι) σ)
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ F.window)
    (G : Control (ι := ι) × M → M)
    (joint : ∃ O : Set (Control (ι := ι)), IsOpen O ∧
      (LeanShared.NoiseCubeRescaling.cube (ι := ι) ε : Set (Control (ι := ι))) ⊆ O ∧
      ContMDiffOn ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) 1 G (O ×ˢ univ))
    (identity : ∀ (a : cube (ι := ι) ε) (y : M),
      ∀ᶠ z in 𝓝 a.val, F.family ε z (G (z, y)) = y)
    (spatial : ∀ (a : cube (ι := ι) ε) (y : M),
      Injective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
        (F.family ε a.val) (G (a.val, y))))
    (L : Laws (ι := ι))
    (hG : Measurable (fun z : M × cube (ι := ι) ε => G (z.2.val, z.1))) :
    ∀ x, LeanShared.RandomMapKernel.transition (L.law ε)
      (fun z : M × cube (ι := ι) ε => G (z.2.val, z.1)) hG x ≪ σ := by
  obtain ⟨C, _hC, bound⟩ := F.inverse_volume_bound_from_submersion σ source ε hε hw G joint identity spatial
  obtain ⟨q, _hq, B, _hB, _hqB, law⟩ := L.bounded_density ε hε
  intro x
  change (L.law ε).map (fun a => G (a.val, x)) ≪ σ
  rw [law]
  exact ((withDensity_absolutelyContinuous (cubeVolume (ι := ι) ε) q).map
    (hG.comp measurable_prodMk_left)).trans (Measure.absolutelyContinuous_of_le_smul (bound x))

variable [SecondCountableTopology M]
  {Parameters : Type*} [MetricSpace Parameters]
  {F : Maps (E := E) (ι := ι) T r} {evaluate : Parameters → M → M}

omit [FiniteDimensional ℝ E] in
theorem Representation.normalized_density_from_submersion
    (p : Representation F Parameters evaluate) (L : Laws (ι := ι))
    (σ : Measure M) [IsFiniteMeasure σ]
    (source : ControlSubmersionSources (E := E) (ι := ι) σ)
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ p.window)
    (K : Set M) (hK : MeasurableSet K) (w : K → ℝ) (hwgt : Measurable w)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (hF : Measurable (fun z : M × FixedControl (ι := ι) =>
      evaluate (p.fixedParameters ε z.2) z.1)) :
    ∃ B : ℝ≥0∞, B ≠ (∞ : ℝ≥0∞) ∧ ∃ q : M × M → ℝ≥0∞,
      Measurable q ∧ (∀ z, q z ≤ B) ∧ ∀ x,
      LeanShared.WeightedConditioning.normalizedKernel
        (LeanShared.RandomMapKernel.killed (L.fixedLaw ε)
          (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) hF K hK)
        (LeanShared.SubtypeKernel.zeroExtend K w) R
        (LeanShared.SubtypeKernel.measurable_zeroExtend K hK w hwgt) x =
          (σ.restrict K).withDensity (fun y => q (x, y)) := by
  obtain ⟨C, hC, bound⟩ := F.volume_bound_from_submersion σ source ε hε (hw.trans p.window_le)
  exact p.exists_bounded_normalized_killed_density L σ ε hε hw C hC bound K hK w hwgt R hR hwR hF

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
