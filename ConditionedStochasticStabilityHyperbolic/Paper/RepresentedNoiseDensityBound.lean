module

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseDensityBound
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedFixedCubeNoise
public import LeanShared.Probability.NormalizedKilledDensity
public import LeanShared.Probability.SubtypeKernel

/-! The constructed bounded transition density is unchanged by exact control
rescaling and the actual analytic map representation. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {T : M ≃ₜ M} {r : ℝ}

omit [FiniteDimensional ℝ E] in
theorem Maps.exists_bounded_fixed_transition_density
    (F : Maps (E := E) (ι := ι) T r) (L : Laws (ι := ι))
    (σ : Measure M) [IsFiniteMeasure σ]
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ F.window)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (volumeBound : ∀ x, (cubeVolume (ι := ι) ε).map
      (fun a : cube (ι := ι) ε => F.family ε a.val x) ≤ C • σ) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∃ q : M × M → ℝ≥0∞,
      Measurable q ∧ (∀ p, q p ≤ B) ∧ ∀ x,
      (L.fixedLaw ε).map (F.fixedMap ε x) = σ.withDensity (fun y => q (x, y)) := by
  obtain ⟨B, hB, q, hq, hb, he⟩ := F.exists_bounded_transition_density L σ ε hε hw C hC volumeBound
  refine ⟨B, hB, q, hq, hb, ?_⟩
  intro x
  have hk := congrArg (fun k : Kernel M M => k x) (F.transition_fixed_cube L ε hε hw)
  exact hk.trans (he x)

variable {Parameters : Type*} [MetricSpace Parameters]
  {F : Maps (E := E) (ι := ι) T r} {evaluate : Parameters → M → M}

omit [FiniteDimensional ℝ E] in
theorem Representation.exists_bounded_fixed_transition_density
    (p : Representation F Parameters evaluate) (L : Laws (ι := ι))
    (σ : Measure M) [IsFiniteMeasure σ]
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ p.window)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (volumeBound : ∀ x, (cubeVolume (ι := ι) ε).map
      (fun a : cube (ι := ι) ε => F.family ε a.val x) ≤ C • σ) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∃ q : M × M → ℝ≥0∞,
      Measurable q ∧ (∀ z, q z ≤ B) ∧ ∀ x,
      (L.fixedLaw ε).map (fun z => evaluate (p.fixedParameters ε z) x) =
        σ.withDensity (fun y => q (x, y)) := by
  obtain ⟨B, hB, q, hq, hb, he⟩ := F.exists_bounded_fixed_transition_density L σ ε hε
    (hw.trans p.window_le) C hC volumeBound
  refine ⟨B, hB, q, hq, hb, ?_⟩
  intro x
  have eq : (fun z => evaluate (p.fixedParameters ε z) x) = F.fixedMap ε x :=
    funext (fun z => p.actual_fixedMap ε hε hw x z)
  rw [eq]
  exact he x

omit [FiniteDimensional ℝ E] in
/-- The exact normalized killed process has a constructed bounded density
relative to the restricted reference. No full boundary support is required. -/
theorem Representation.exists_bounded_normalized_killed_density
    (p : Representation F Parameters evaluate) (L : Laws (ι := ι))
    (σ : Measure M) [IsFiniteMeasure σ]
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ p.window)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (volumeBound : ∀ x, (cubeVolume (ι := ι) ε).map
      (fun a : cube (ι := ι) ε => F.family ε a.val x) ≤ C • σ)
    (K : Set M) (hK : MeasurableSet K) (w : K → ℝ) (hwgt : Measurable w)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (hF : Measurable (fun z : M × FixedControl (ι := ι) =>
      evaluate (p.fixedParameters ε z.2) z.1)) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∃ q : M × M → ℝ≥0∞,
      Measurable q ∧ (∀ z, q z ≤ B) ∧ ∀ x,
      LeanShared.WeightedConditioning.normalizedKernel
        (LeanShared.RandomMapKernel.killed (L.fixedLaw ε)
          (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) hF K hK)
        (LeanShared.SubtypeKernel.zeroExtend K w) R
        (LeanShared.SubtypeKernel.measurable_zeroExtend K hK w hwgt) x =
          (σ.restrict K).withDensity (fun y => q (x, y)) := by
  obtain ⟨B, hB, q, hq, hb, he⟩ := p.exists_bounded_fixed_transition_density L σ ε hε hw C hC volumeBound
  have hz := LeanShared.SubtypeKernel.zeroExtend_le K w R hR.le hwR
  obtain ⟨q', hq', hb', he'⟩ := LeanShared.NormalizedKilledDensity.exists_density
    (L.fixedLaw ε) (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) hF
    σ q hq he B hb K hK (LeanShared.SubtypeKernel.zeroExtend K w)
    (LeanShared.SubtypeKernel.measurable_zeroExtend K hK w hwgt) R hR hz
  exact ⟨B, hB, q', hq', hb', he'⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
