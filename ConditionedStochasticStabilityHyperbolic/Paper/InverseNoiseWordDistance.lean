module
public import ConditionedStochasticStabilityHyperbolic.Paper.ConstructedInverseNoiseFamily
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseUniformWindow
public import LeanShared.Dynamics.RobustFiniteIsolation

/-! Uniform inverse finite-word closeness, using the proved inverse modulus
rather than a fictitious linear Whitney rate. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set
open scoped Topology NNReal
open LeanShared.FiniteJetComposition

theorem InverseFamily.exists_uniform_word_distance
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F)
    (N : ℕ) (δ : ℝ) (positive : 0 < δ) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∀ controls : ℕ → cube (ι := ι) ε, ∀ x : M,
      dist (word (fun n y => J.map ε ((controls n).val,y)) N x) ((T.symm : M → M)^[N] x) < δ := by
  obtain ⟨ξ,positiveξ,close⟩ := LeanShared.exists_uniform_finite_orbit_closeness
    (CompactSpace.uniformContinuous_of_continuous T.symm.continuous) N positive
  obtain ⟨η,positiveη,_windowη,uniform⟩ := F.inverse_uniform_window ξ positiveξ
  refine ⟨min η J.window,lt_min positiveη J.positive,fun ε hp hw controls x => ?_⟩
  have small := hw.trans (min_le_right _ _)
  exact close (fun n => word (fun j y => J.map ε ((controls j).val,y)) n x)
    (fun n _ => uniform ε hp (hw.trans (min_le_left _ _)) (controls n)
      (fun y => J.map ε ((controls n).val,y))
      (J.right ε hp small _ (J.contains ε hp small (controls n).property)) _) N le_rfl

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
