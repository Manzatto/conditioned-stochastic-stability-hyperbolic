module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseGlobalInjectivity
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseGlobalSurjectivity
public import ConditionedStochasticStabilityHyperbolic.Paper.FixedCubeNoise
public import LeanShared.Topology.CompactParametricInverse

/-! The actual small perturbations are genuine homeomorphisms, and their
inverse action is jointly continuous in the original control and state.
No inverse maps, injectivity, surjectivity or inverse continuity are inputs. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold
open scoped Topology Manifold ContDiff NNReal

set_option maxHeartbeats 2400000 in
theorem Maps.exists_actual_homeomorphisms
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm) :
    ∃ η : ℝ≥0, 0 < η ∧ η ≤ F.window ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∃ H : cube (ι := ι) ε → M ≃ₜ M,
        (∀ a x, H a x = F.family ε a.val x) ∧
        Continuous (fun p : cube (ι := ι) ε × M => (H p.1).symm p.2) := by
  classical
  obtain ⟨ηi,positiveηi,injective⟩ := F.exists_global_injectivity_window regularity deterministic inverse
  obtain ⟨ηs,positiveηs,surjective⟩ := F.exists_global_surjectivity_window regularity deterministic inverse
  refine ⟨min F.window (min ηi ηs),lt_min F.window_positive (lt_min positiveηi positiveηs),
    min_le_left _ _,fun ε hp hw => ?_⟩
  let e (a : cube (ι := ι) ε) : M ≃ M := Equiv.ofBijective (F.family ε a.val)
    ⟨injective ε hp (hw.trans ((min_le_right _ _).trans (min_le_left _ _))) a,
      surjective ε hp (hw.trans ((min_le_right _ _).trans (min_le_right _ _))) a⟩
  have forward (a : cube (ι := ι) ε) : Continuous (e a) :=
    (F.raw_continuous ε hp (hw.trans (min_le_left _ _))).comp (continuous_id.prodMk continuous_const)
  let H : cube (ι := ι) ε → M ≃ₜ M := fun a => (forward a).homeoOfEquivCompactToT2
  refine ⟨H,fun _ _ => rfl,?_⟩
  exact LeanShared.CompactParametricInverse.continuous_inverse e
    ((F.raw_continuous ε hp (hw.trans (min_le_left _ _))).comp continuous_swap)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
