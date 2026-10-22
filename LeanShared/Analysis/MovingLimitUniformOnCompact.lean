module
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Tactic.Positivity

/-! A moving-point limit, uniform over arbitrary controls, gives one positive
noise window on a compact set. No parameter continuity is required. -/
public noncomputable section
namespace LeanShared.MovingLimitUniformOnCompact
open Set Filter
open scoped Topology NNReal

theorem uniform
    {X Y : Type*} [MetricSpace X] [NormedAddCommGroup Y]
    (Ω : ℝ≥0 → Type*) (f : (ε : ℝ≥0) → Ω ε → X → Y) (g : X → Y)
    (U K : Set X) (compact : IsCompact K) (subset : K ⊆ U)
    (continuous : ContinuousOn g U)
    (converges : ∀ (ε : ℕ → ℝ≥0) (ω : ∀ n, Ω (ε n)),
      Tendsto ε atTop (𝓝 0) → (∀ n, 0 < ε n) →
      ∀ p ∈ U, ∀ x : ℕ → X, Tendsto x atTop (𝓝 p) →
        Tendsto (fun n => f (ε n) (ω n) (x n)) atTop (𝓝 (g p)))
    (δ : ℝ) (positive : 0 < δ) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ ω : Ω ε,
      ∀ x ∈ K, ‖f ε ω x - g x‖ ≤ δ := by
  by_contra! failure
  have failures (n : ℕ) :
      ∃ ε : ℝ≥0, 0 < ε ∧ ε ≤ 1 / ((n : ℝ≥0) + 1) ∧ ∃ ω : Ω ε,
        ∃ x ∈ K, δ < ‖f ε ω x - g x‖ :=
    failure (1 / ((n : ℝ≥0) + 1)) (by positivity)
  choose ε positiveε small ω x inside bad using failures
  have limitε : Tendsto ε atTop (𝓝 0) := by
    apply NNReal.tendsto_coe.mp
    exact squeeze_zero (fun n => (ε n).property)
      (fun n => by exact_mod_cast small n) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨p, hp, φ, increasing, limitx⟩ := compact.tendsto_subseq inside
  have noisy := converges (ε ∘ φ) (fun n => ω (φ n))
    (limitε.comp increasing.tendsto_atTop) (fun n => positiveε (φ n))
    p (subset hp) (x ∘ φ) limitx
  have value : Tendsto (fun n => g (x (φ n))) atTop (𝓝 (g p)) :=
    (continuous p (subset hp)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨limitx,Eventually.of_forall (fun n => subset (inside (φ n)))⟩)
  have total : Tendsto (fun n => ‖f (ε (φ n)) (ω (φ n)) (x (φ n)) - g (x (φ n))‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply,sub_self,norm_zero] using (noisy.sub value).norm
  obtain ⟨n,hn⟩ := (total.eventually (gt_mem_nhds positive)).exists
  exact (not_lt_of_ge hn.le) (bad (φ n))

end LeanShared.MovingLimitUniformOnCompact
