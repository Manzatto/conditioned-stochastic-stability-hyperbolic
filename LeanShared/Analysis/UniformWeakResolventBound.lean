module

public import LeanShared.Analysis.TwoNormResolventWeakBound
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-! Uniform weak-resolvent estimates with arbitrarily small strong remainder,
proved from actual two-norm growth and deterministic resolvent norm bounds. -/

public section
open Filter Topology
namespace LeanShared.UniformWeakResolventBound
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- On a bounded outer annulus with bounded actual resolvent, its weak norm
has an arbitrarily small strong contribution and a finite weak contribution.
This is the absorption estimate used in the KL resolvent argument. -/
theorem exists_bound (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (α M C D Cw r outer L : ℝ)
    (hα : 0 ≤ α) (hM : 0 ≤ M) (hC : 0 ≤ C) (hD : 0 ≤ D) (hCw : 0 ≤ Cw)
    (hr : α < r) (houter : 0 ≤ outer) (hL : 0 ≤ L)
    (strong : ∀ k x, ‖(T ^ k) x‖ ≤ C * α ^ k * ‖x‖ + D * M ^ k * ‖i x‖)
    (weak : ∀ k x, ‖i ((T ^ k) x)‖ ≤ Cw * M ^ k * ‖i x‖)
    (η : ℝ) (hη : 0 < η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ outer →
      z ∈ resolventSet ℂ T → ‖resolvent T z‖ ≤ L → ∀ x : E,
      ‖i ((resolvent T z) x)‖ ≤ η * ‖x‖ + B * ‖i x‖ := by
  have hrpos : 0 < r := hα.trans_lt hr
  have ratio : α / r < 1 := (div_lt_one hrpos).mpr hr
  have tend : Tendsto (fun n : ℕ => (‖i‖ * L * C) * (α / r) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hα hrpos.le) ratio).const_mul (‖i‖ * L * C)
  obtain ⟨n, hn⟩ := (tend.eventually (gt_mem_nhds hη)).exists
  let poly := ∑ k ∈ Finset.range n, outer ^ (n - 1 - k) * (Cw * M ^ k)
  have hpoly : 0 ≤ poly := Finset.sum_nonneg (fun _ _ => by positivity)
  let B := (‖i‖ * L * D) * (M / r) ^ n + poly / r ^ n
  refine ⟨B, by positivity, fun z hlow hhigh hres hresnorm x => ?_⟩
  have hzpos : 0 < ‖z‖ := hrpos.trans_le hlow
  have hz : z ≠ 0 := norm_pos_iff.mp hzpos
  have ratioA : α / ‖z‖ ≤ α / r := div_le_div₀ hα le_rfl hrpos hlow
  have ratioM : M / ‖z‖ ≤ M / r := div_le_div₀ hM le_rfl hrpos hlow
  have coefA : (‖i‖ * ‖resolvent T z‖ * C) * (α / ‖z‖) ^ n ≤
      (‖i‖ * L * C) * (α / r) ^ n := by gcongr
  have coefM : (‖i‖ * ‖resolvent T z‖ * D) * (M / ‖z‖) ^ n ≤
      (‖i‖ * L * D) * (M / r) ^ n := by gcongr
  have sumBound : (∑ k ∈ Finset.range n, ‖z‖ ^ (n - 1 - k) * (Cw * M ^ k)) ≤ poly := by
    apply Finset.sum_le_sum
    intro k _
    gcongr
  have polynomial : (∑ k ∈ Finset.range n, ‖z‖ ^ (n - 1 - k) * (Cw * M ^ k)) / ‖z‖ ^ n ≤
      poly / r ^ n := div_le_div₀ hpoly sumBound (pow_pos hrpos n) (pow_le_pow_left₀ hrpos.le hlow n)
  exact (TwoNormResolventWeakBound.resolvent_bound T i α M C D Cw strong weak z hz hres n x).trans
    (add_le_add (mul_le_mul_of_nonneg_right (coefA.trans hn.le) (norm_nonneg x))
      (mul_le_mul_of_nonneg_right (add_le_add coefM polynomial) (norm_nonneg (i x))))

end LeanShared.UniformWeakResolventBound
