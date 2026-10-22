module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseWordDistance
public import LeanShared.Topology.CompactNearDiagonalContinuity

/-! Actual noisy N-step words remain in every prescribed open target of a
compact deterministic N-step image, uniformly in all controls and starts. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set
open scoped Topology NNReal
open LeanShared.FiniteJetComposition

theorem InverseFamily.exists_uniform_word_target
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F)
    (N : ℕ) (K U : Set M) (compact : IsCompact K) (openU : IsOpen U)
    (target : MapsTo ((T.symm : M → M)^[N]) K U) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∀ controls : ℕ → cube (ι := ι) ε, MapsTo
        (word (fun n => fun w => J.map ε ((controls n).val,w)) N) K U := by
  have imageCompact := compact.image (T.symm.continuous.iterate N)
  have imageInside : (T.symm : M → M)^[N] '' K ⊆ U := by
    rintro _ ⟨x,hx,rfl⟩
    exact target hx
  obtain ⟨δ, positiveδ, neighborhood⟩ := LeanShared.CompactNearDiagonalContinuity.exists_radius
    _ U imageCompact openU imageInside id continuousOn_id 1 zero_lt_one
  obtain ⟨η, positiveη, close⟩ := J.exists_uniform_word_distance N δ positiveδ
  refine ⟨η, positiveη, fun ε hp hw controls x hx => ?_⟩
  exact (neighborhood ((T.symm : M → M)^[N] x) (mem_image_of_mem _ hx) _
    (by simpa only [dist_comm] using close ε hp hw controls x)).1

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
