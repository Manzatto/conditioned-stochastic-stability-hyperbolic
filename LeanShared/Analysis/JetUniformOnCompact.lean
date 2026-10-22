module
public import LeanShared.Analysis.FiniteJetComposition
import all LeanShared.Analysis.FiniteJetComposition
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Positivity

/-! Moving-point C¹ convergence yields a single uniform positive-noise
window on a compact set. The varying index may contain arbitrary controls;
no continuity of the family in noise scale or choice of controls is assumed. -/
public noncomputable section
namespace LeanShared.FiniteJetComposition
open Set Filter
open scoped Topology NNReal

theorem uniform_on_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω : ℝ≥0 → Type*) (f : (ε : ℝ≥0) → Ω ε → E → F) (g : E → F)
    (U K : Set E) (compact : IsCompact K) (subset : K ⊆ U)
    (smooth : ∀ x ∈ U, ContDiffAt ℝ 1 g x)
    (converges : ∀ (ε : ℕ → ℝ≥0) (ω : ∀ n, Ω (ε n)),
      Tendsto ε atTop (𝓝 0) → (∀ n, 0 < ε n) →
      JetConvergesOn (fun n => f (ε n) (ω n)) g atTop U)
    (δ : ℝ) (positive : 0 < δ) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ ω : Ω ε,
      ∀ x ∈ K, ‖f ε ω x - g x‖ + ‖fderiv ℝ (f ε ω) x - fderiv ℝ g x‖ ≤ δ := by
  by_contra! failure
  have failures (n : ℕ) :
      ∃ ε : ℝ≥0, 0 < ε ∧ ε ≤ 1 / ((n : ℝ≥0) + 1) ∧ ∃ ω : Ω ε,
        ∃ x ∈ K, δ < ‖f ε ω x - g x‖ + ‖fderiv ℝ (f ε ω) x - fderiv ℝ g x‖ :=
    failure (1 / ((n : ℝ≥0) + 1)) (by positivity)
  choose ε positiveε small ω x inside bad using failures
  have limitε : Tendsto ε atTop (𝓝 0) := by
    apply NNReal.tendsto_coe.mp
    exact squeeze_zero (fun n => (ε n).property)
      (fun n => by exact_mod_cast small n) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨p, hp, φ, increasing, limitx⟩ := compact.tendsto_subseq inside
  have subsequenceε := limitε.comp increasing.tendsto_atTop
  have jets := converges (ε ∘ φ) (fun n => ω (φ n)) subsequenceε
    (fun n => positiveε (φ n))
  have noisy := (jets p (subset hp)).2 (x ∘ φ) limitx
  have value := (smooth p (subset hp)).continuousAt.tendsto.comp limitx
  have derivative := ((smooth p (subset hp)).continuousAt_fderiv (by norm_num)).tendsto.comp limitx
  have total : Tendsto (fun n =>
      ‖f (ε (φ n)) (ω (φ n)) (x (φ n)) - g (x (φ n))‖ +
      ‖fderiv ℝ (f (ε (φ n)) (ω (φ n))) (x (φ n)) - fderiv ℝ g (x (φ n))‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self, norm_zero, zero_add] using
      ((noisy.1.sub value).norm.add (noisy.2.1.sub derivative).norm)
  obtain ⟨n, hn⟩ := (total.eventually (gt_mem_nhds positive)).exists
  exact (not_lt_of_ge hn.le) (bad (φ n))

end LeanShared.FiniteJetComposition
