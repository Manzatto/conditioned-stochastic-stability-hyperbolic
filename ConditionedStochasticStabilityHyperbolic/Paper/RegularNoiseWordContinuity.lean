module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
public import LeanShared.Analysis.FiniteJetWords

/-! Joint continuity of actual finite noisy words in their control sequence
and starting state, derived from the literal joint C¹ noise hypothesis. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set
open scoped Topology Manifold ContDiff NNReal
open LeanShared.FiniteJetComposition

theorem Maps.cube_map_continuous
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window) :
    Continuous (fun z : cube (ι := ι) ε × M => F.family ε z.1.val z.2) := by
  obtain ⟨O, _openO, contains, smooth⟩ := F.joint_C1 ε positive window
  have embed : Continuous (fun z : cube (ι := ι) ε × M => (z.1.val, z.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  exact continuousOn_univ.mp (smooth.continuousOn.comp embed.continuousOn
    (fun z _ => ⟨contains z.1.property, mem_univ _⟩))

theorem Maps.word_continuous
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window) (N : ℕ) :
    Continuous (fun z : (ℕ → cube (ι := ι) ε) × M =>
      word (fun n => F.family ε (z.1 n).val) N z.2) := by
  induction N with
  | zero => exact continuous_snd
  | succ n ih =>
    exact (F.cube_map_continuous ε positive window).comp
      (((continuous_apply n).comp continuous_fst).prodMk ih)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
