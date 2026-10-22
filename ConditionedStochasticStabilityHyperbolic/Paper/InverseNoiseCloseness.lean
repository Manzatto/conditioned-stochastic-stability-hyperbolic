module

public import ConditionedStochasticStabilityHyperbolic.Paper.InverseCubeGeometry
public import LeanShared.Dynamics.BackwardIsolation

/-! Forward Whitney closeness supplies a common inverse-map tolerance before
choosing the driving law or any density/eigenfunction. -/

@[expose] public noncomputable section
open Set Metric
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
  {T : M ≃ₜ M} {r : ℝ}

omit [FiniteDimensional ℝ E] in
theorem Maps.inverse_closeness_threshold (F : Maps (E := E) (ι := ι) T r)
    (η : ℝ) (hη : 0 < η) : ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ F.window → (ε : ℝ) < ε₀ →
      ∀ V G : Set M, ∀ d : InverseCubeGeometry F ε V G,
      ∀ x : M, ∀ a : cube (ι := ι) ε, dist (d.actualMap (x, a)) (T.symm x) < η := by
  obtain ⟨δ, hδ, inverse⟩ := exists_uniform_inverse_step_tolerance T
    (CompactSpace.uniformContinuous_of_continuous T.symm.continuous) hη
  have hc : 0 < F.constant + 1 := by linarith [F.constant_positive]
  refine ⟨δ / (F.constant + 1), div_pos hδ hc, ?_⟩
  intro ε hε hw he V G d x a
  apply inverse (d.actualMap (x, a)) x
  have hid := (d.identity a x).self_of_nhds
  have hb := F.uniform_close ε hε hw a (d.actualMap (x, a))
  have hp : (ε : ℝ) * (F.constant + 1) < δ := (lt_div_iff₀ hc).mp he
  change F.family ε a.val (d.actualMap (x, a)) = x at hid
  rw [hid, dist_comm] at hb
  exact hb.trans_lt (by nlinarith [show (0 : ℝ) < ε from hε])

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
