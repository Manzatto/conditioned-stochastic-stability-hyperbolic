module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
public import LeanShared.Analysis.FiniteJetWords
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Every actual finite noisy word converges at moving initial points to the
corresponding deterministic iterate. No continuity in noise scale or choice
of driving laws is required; the original uniform Whitney bound suffices. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter
open scoped Topology NNReal
open LeanShared.FiniteJetComposition

theorem Maps.moving_map_tendsto
    {E M ι A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (ε : A → ℝ≥0) (controls : ∀ a, cube (ι := ι) (ε a)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ a in l, 0 < ε a)
    (v : A → M) (x : M) (moving : Tendsto v l (𝓝 x)) :
    Tendsto (fun a => F.family (ε a) (controls a).val (v a)) l (𝓝 (T x)) := by
  have window : ∀ᶠ a in l, ε a ≤ F.window :=
    (limit.eventually (gt_mem_nhds F.window_positive)).mono (fun _ h => h.le)
  have realLimit : Tendsto (fun a => (ε a : ℝ)) l (𝓝 0) := by
    exact_mod_cast (NNReal.continuous_coe.continuousAt.tendsto.comp limit)
  have boundLimit : Tendsto (fun a => F.constant * (ε a : ℝ)) l (𝓝 0) := by
    simpa only [mul_zero] using realLimit.const_mul F.constant
  have distance : Tendsto (fun a => dist (T (v a))
      (F.family (ε a) (controls a).val (v a))) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ boundLimit
    filter_upwards [positive, window] with a ha hw
    rw [dist_comm]
    exact F.uniform_close (ε a) ha hw (controls a) (v a)
  exact (T.continuous.continuousAt.tendsto.comp moving).congr_dist distance

theorem Maps.moving_word_tendsto
    {E M ι A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (ε : A → ℝ≥0) (controls : ℕ → ∀ a, cube (ι := ι) (ε a)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ a in l, 0 < ε a)
    (v : A → M) (x : M) (moving : Tendsto v l (𝓝 x)) (N : ℕ) :
    Tendsto (fun a => word (fun n => F.family (ε a) (controls n a).val) N (v a)) l
      (𝓝 ((T : M → M)^[N] x)) := by
  induction N with
  | zero => exact moving
  | succ n ih =>
    simpa only [word, Function.comp_apply, Function.iterate_succ_apply'] using
      F.moving_map_tendsto ε (controls n) l limit positive _ _ ih

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
