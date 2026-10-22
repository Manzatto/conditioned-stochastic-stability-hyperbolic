module

public import ConditionedStochasticStabilityHyperbolic.Paper.FixedCubeNoise
public import LeanShared.Probability.DominatedKernelDensity

/-! An ordinary law-independent cube-volume domination estimate constructs
joint bounded transition densities for EVERY admissible L∞ noise law. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {T : M ≃ₜ M} {r : ℝ}

omit [FiniteDimensional ℝ E] in
theorem Maps.exists_bounded_transition_density
    (F : Maps (E := E) (ι := ι) T r) (L : Laws (ι := ι))
    (σ : Measure M) [IsFiniteMeasure σ]
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ F.window)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (volumeBound : ∀ x, (cubeVolume (ι := ι) ε).map
      (fun a : cube (ι := ι) ε => F.family ε a.val x) ≤ C • σ) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∃ q : M × M → ℝ≥0∞,
      Measurable q ∧ (∀ p, q p ≤ B) ∧ ∀ x,
      (L.law ε).map (fun a => F.family ε a.val x) = σ.withDensity (fun y => q (x, y)) := by
  have : IsProbabilityMeasure (L.law ε) := L.probability ε
  obtain ⟨p, hp, B, hB, hpB, law⟩ := L.bounded_density ε hε
  have lawle : L.law ε ≤ B • cubeVolume (ι := ι) ε := by
    rw [law, ← withDensity_const]
    exact withDensity_mono (ae_of_all _ hpB)
  let H : M × cube (ι := ι) ε → M := fun z => F.family ε z.2.val z.1
  have hH : Measurable H := (F.raw_continuous ε hε hw).measurable
  let κ := LeanShared.RandomMapKernel.transition (L.law ε) H hH
  have dom : ∀ x, κ x ≤ (B * C) • σ := by
    intro x
    have hx : Measurable (fun a : cube (ι := ι) ε => F.family ε a.val x) :=
      hH.comp (measurable_const.prodMk measurable_id)
    have hm := Measure.map_mono lawle hx
    rw [Measure.map_smul B hx.aemeasurable] at hm
    change (L.law ε).map (fun a => F.family ε a.val x) ≤ _
    apply hm.trans
    rw [← smul_smul]
    gcongr
    exact volumeBound x
  obtain ⟨q, hq, hb, he⟩ := LeanShared.DominatedKernelDensity.exists_bounded_density
    κ σ (B * C) (ENNReal.mul_ne_top hB hC) dom
  exact ⟨B * C, ENNReal.mul_ne_top hB hC, q, hq, hb, he⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
