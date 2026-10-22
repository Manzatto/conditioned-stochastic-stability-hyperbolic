module
public import ConditionedStochasticStabilityHyperbolic.Paper.ConstructedInverseNoiseFamily
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseUniformWindow
public import LeanShared.Dynamics.BackwardTailLocalization

/-! Compact isolation localizes every inverse-noise backward tail, uniformly
before all original controls and trajectories, using the actual inverse
modulus rather than a presumed linear inverse Whitney bound. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set
open scoped Topology NNReal

theorem InverseFamily.exists_uniform_backward_tail
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F)
    {K U : Set M} (compact : IsCompact K) (openU : IsOpen U)
    (core : LeanShared.isolatedCore T.symm K ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∀ controls : ℕ → cube (ι := ι) ε, ∀ b : ℕ → M,
      (∀ n, b n ∈ K) → (∀ n, J.map ε ((controls n).val,b (n+1)) = b n) →
      ∀ n, N ≤ n → b n ∈ U := by
  obtain ⟨N,positiveN,δ,positiveδ,localize⟩ :=
    LeanShared.exists_uniform_backward_tail_localization T.symm
      (CompactSpace.uniformContinuous_of_continuous T.symm.continuous)
      (CompactSpace.uniformContinuous_of_continuous T.continuous) compact openU core
  obtain ⟨η,positiveη,_windowη,close⟩ := F.inverse_uniform_window δ positiveδ
  refine ⟨N,positiveN,min η J.window,lt_min positiveη J.positive,fun ε hp hw controls b inside step => ?_⟩
  have small := hw.trans (min_le_right _ _)
  apply localize b inside
  intro n
  rw [← step n]
  exact close ε hp (hw.trans (min_le_left _ _)) (controls n)
    (fun y => J.map ε ((controls n).val,y))
    (J.right ε hp small _ (J.contains ε hp small (controls n).property)) _

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
