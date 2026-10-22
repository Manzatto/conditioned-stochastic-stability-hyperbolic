module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseMapImage

/-! Every letter of the common map space is a literal positive-scale noise
map: the deterministic reference is the zero control at the top scale. -/
public noncomputable section
open Set
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.MapImage
open LeanShared
variable {E M ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace M] [CompactSpace M]
  [ChartedSpace E M] {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
  (hr : 1 ≤ r) (η : ℝ≥0) (hw : η ≤ F.window)

omit [CompactSpace M] in
theorem maps_noise (ε : ℝ≥0) (hp : 0 < ε) (hl : ε ≤ η) (control : cube (ι := ι) ε) :
    maps F hr η hw (noise F hr η hw ε hp hl control) = F.family ε control.val := rfl

omit [CompactSpace M] in
theorem exists_family (positive : 0 < η) (a : Space F hr η hw) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ε ≤ η ∧ ∃ control : cube (ι := ι) ε,
      maps F hr η hw a = F.family ε control.val := by
  rw [← representative_maps F hr η hw a]
  cases representative F hr η hw a with
  | none =>
    have zero : (0 : Control (ι := ι)) ∈ (NoiseCubeRescaling.cube (ι := ι) (η : ℝ) : Set (Control (ι := ι))) := by
      intro i
      simp
    exact ⟨η, positive, le_rfl, ⟨0, zero⟩,
      funext fun x => (F.zero_control η positive hw x).symm⟩
  | some p => exact ⟨p.1.val, p.1.property.1, p.1.property.2, p.2, rfl⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise.MapImage
