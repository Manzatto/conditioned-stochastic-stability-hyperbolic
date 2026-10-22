module
public import ConditionedStochasticStabilityHyperbolic.Paper.ConstructedInverseNoiseFamily
public import LeanShared.Analysis.FiniteJetWords

/-! Joint continuity of actual finite noisy words in their control sequence
and starting state, derived from the literal joint C¹ noise hypothesis. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set
open scoped Topology Manifold ContDiff NNReal
open LeanShared.FiniteJetComposition

theorem InverseFamily.cube_map_continuous
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F)
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ J.window) :
    Continuous (fun z : cube (ι := ι) ε × M => J.map ε (z.1.val,z.2)) := by
  have smooth := J.smooth ε positive window
  have contains := J.contains ε positive window
  have embed : Continuous (fun z : cube (ι := ι) ε × M => (z.1.val, z.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  exact continuousOn_univ.mp (smooth.continuousOn.comp embed.continuousOn
    (fun z _ => ⟨contains z.1.property, mem_univ _⟩))

theorem InverseFamily.word_continuous
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F)
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ J.window) (N : ℕ) :
    Continuous (fun z : (ℕ → cube (ι := ι) ε) × M =>
      word (fun n => fun y => J.map ε ((z.1 n).val,y)) N z.2) := by
  induction N with
  | zero => exact continuous_snd
  | succ n ih =>
    exact (J.cube_map_continuous ε positive window).comp
      (((continuous_apply n).comp continuous_fst).prodMk ih)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
