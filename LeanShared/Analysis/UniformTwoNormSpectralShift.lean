module

public import LeanShared.Analysis.TwoNormSpectralShift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform Peetre estimates on annuli for whole families satisfying common
two-norm growth and a common one-step operator bound. -/

public section
open Filter Topology ContinuousLinearMap
namespace LeanShared.UniformTwoNormSpectralShift
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Common Lasota–Yorke constants and a common operator bound give uniform
strong/weak Peetre constants on an outer annulus. -/
theorem exists_annulus_bound (i : E →L[ℂ] W) (α M C D r outer bound : ℝ)
    (hα : 0 ≤ α) (hM : 0 ≤ M) (hD : 0 ≤ D) (hr : α < r)
    (houter : 0 ≤ outer) (hbound : 0 ≤ bound) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ T : E →L[ℂ] E, ‖T‖ ≤ bound →
      (∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * M ^ n * ‖i x‖) →
      ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ outer → ∀ x : E,
        ‖x‖ ≤ A * ‖i x‖ + B * ‖(T - z • 1) x‖ := by
  classical
  by_cases trivial : Subsingleton E
  · let _ : Subsingleton E := trivial
    refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
    intro T _ _ z _ _ x
    simp [Subsingleton.elim x 0]
  let : Nontrivial E := not_subsingleton_iff_nontrivial.mp trivial
  have hrpos : 0 < r := hα.trans_lt hr
  have hratio : α / r < 1 := (div_lt_one hrpos).mpr hr
  have tend : Tendsto (fun n : ℕ => C * (α / r) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hα hrpos.le) hratio).const_mul C
  obtain ⟨n, hn⟩ := (tend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
  have hn' : C * α ^ n < r ^ n := by
    have eq : C * (α / r) ^ n = (C * α ^ n) / r ^ n := by rw [div_pow]; ring
    rw [eq] at hn
    simpa only [one_mul] using (div_lt_iff₀ (pow_pos hrpos n)).mp hn
  let gap := r ^ n - C * α ^ n
  have hgap : 0 < gap := sub_pos.mpr hn'
  let K := ∑ k ∈ Finset.range n, bound ^ k * outer ^ (n - 1 - k)
  have hK : 0 ≤ K := Finset.sum_nonneg (fun k _ =>
    mul_nonneg (pow_nonneg hbound k)
      (pow_nonneg houter _))
  refine ⟨D * M ^ n / gap, K / gap, by positivity, by positivity, ?_⟩
  intro T hT estimate z hzlow hzhigh x
  have factor : (T ^ n) x - (z ^ n) • x = (TwoNormSpectralShift.powerSum T z n) ((T - z • 1) x) := by
    have hh := congrArg (fun Q : E →L[ℂ] E => Q x) (TwoNormSpectralShift.powerSum_factor T z n)
    simpa only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] using hh.symm
  have herr : ‖(T ^ n) x - (z ^ n) • x‖ ≤ K * ‖(T - z • 1) x‖ := by
    rw [factor]
    have hpoly : ‖TwoNormSpectralShift.powerSum T z n‖ ≤ K := by
      have first := TwoNormSpectralShift.norm_powerSum_le T n outer z hzhigh
      simp only [norm_one, mul_one] at first
      apply first.trans
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg T) hT k)
        (pow_nonneg houter _)
    exact ((TwoNormSpectralShift.powerSum T z n).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hpoly (norm_nonneg _))
  have hmain : ‖z‖ ^ n * ‖x‖ ≤ ‖(T ^ n) x‖ + ‖(T ^ n) x - (z ^ n) • x‖ := by
    simpa only [norm_smul, norm_pow] using
      norm_le_norm_add_norm_sub ((T ^ n) x) ((z ^ n) • x)
  have hlower := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hrpos.le hzlow n) (norm_nonneg x)
  calc
    ‖x‖ ≤ (D * M ^ n * ‖i x‖ + K * ‖(T - z • 1) x‖) / gap :=
      (le_div_iff₀ hgap).mpr (by dsimp only [gap]; nlinarith [estimate n x])
    _ = _ := by ring

end LeanShared.UniformTwoNormSpectralShift
