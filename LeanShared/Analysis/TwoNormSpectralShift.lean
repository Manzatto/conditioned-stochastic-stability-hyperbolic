module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform strong/weak spectral-shift estimates on compact annuli outside
the strong Lasota–Yorke growth disk. No compact embedding or spectral source
is needed for this quantitative step of the KL resolvent argument. -/

public noncomputable section
open Filter Topology ContinuousLinearMap
namespace LeanShared.TwoNormSpectralShift
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The actual polynomial in the factorization of a difference of powers. -/
def powerSum (T : E →L[ℂ] E) (z : ℂ) (n : ℕ) : E →L[ℂ] E :=
  ∑ k ∈ Finset.range n, T ^ k * (z • (1 : E →L[ℂ] E)) ^ (n - 1 - k)

/-- Right factorization, in an operator algebra with no commutativity assumption. -/
theorem powerSum_factor (T : E →L[ℂ] E) (z : ℂ) (n : ℕ) :
    powerSum T z n * (T - z • 1) = T ^ n - (z ^ n) • 1 := by
  have comm : Commute T (z • (1 : E →L[ℂ] E)) := by
    change T * (z • 1) = (z • 1) * T
    simpa only [Algebra.algebraMap_eq_smul_one] using (Algebra.commutes z T).symm
  simpa only [powerSum, smul_pow, one_pow] using comm.geom_sum₂_mul n

/-- A bound uniform over the outer radius of a spectral annulus. -/
theorem norm_powerSum_le [Nontrivial E] (T : E →L[ℂ] E) (n : ℕ) (M : ℝ)
    (z : ℂ) (hz : ‖z‖ ≤ M) :
    ‖powerSum T z n‖ ≤
      ∑ k ∈ Finset.range n, ‖T‖ ^ k * (M * ‖(1 : E →L[ℂ] E)‖) ^ (n - 1 - k) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hs : ‖z • (1 : E →L[ℂ] E)‖ ≤ M * ‖(1 : E →L[ℂ] E)‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  exact (norm_mul_le _ _).trans (mul_le_mul
    (norm_pow_le T k)
    ((norm_pow_le (z • (1 : E →L[ℂ] E)) _).trans
      (pow_le_pow_left₀ (norm_nonneg _) hs _))
    (norm_nonneg _) (pow_nonneg (norm_nonneg T) k))

/-- Uniform Peetre-type estimate on an annulus outside the strong growth disk.
It holds for arbitrary bounded operators with the stated all-power estimate;
no resolvent existence is included in the premises. -/
theorem exists_annulus_bound (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (α R C D r M : ℝ) (hα : 0 ≤ α) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hr : α < r) (hM : 0 ≤ M)
    (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ M → ∀ x : E,
      ‖x‖ ≤ A * ‖i x‖ + B * ‖(T - z • 1) x‖ := by
  classical
  by_cases trivial : Subsingleton E
  · let _ : Subsingleton E := trivial
    refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
    intro z _ _ x
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
  let K := ∑ k ∈ Finset.range n, ‖T‖ ^ k * (M * ‖(1 : E →L[ℂ] E)‖) ^ (n - 1 - k)
  have hK : 0 ≤ K := Finset.sum_nonneg (fun k _ =>
    mul_nonneg (pow_nonneg (norm_nonneg T) k)
      (pow_nonneg (mul_nonneg hM (norm_nonneg _)) _))
  refine ⟨D * R ^ n / gap, K / gap, by positivity, by positivity, ?_⟩
  intro z hzlow hzhigh x
  have factor : (T ^ n) x - (z ^ n) • x = (powerSum T z n) ((T - z • 1) x) := by
    have hh := congrArg (fun Q : E →L[ℂ] E => Q x) (powerSum_factor T z n)
    simpa only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] using hh.symm
  have herr : ‖(T ^ n) x - (z ^ n) • x‖ ≤ K * ‖(T - z • 1) x‖ := by
    rw [factor]
    exact ((powerSum T z n).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (norm_powerSum_le T n M z hzhigh) (norm_nonneg _))
  have hmain : ‖z‖ ^ n * ‖x‖ ≤ ‖(T ^ n) x‖ + ‖(T ^ n) x - (z ^ n) • x‖ := by
    simpa only [norm_smul, norm_pow] using
      norm_le_norm_add_norm_sub ((T ^ n) x) ((z ^ n) • x)
  have hlower := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hrpos.le hzlow n) (norm_nonneg x)
  calc
    ‖x‖ ≤ (D * R ^ n * ‖i x‖ + K * ‖(T - z • 1) x‖) / gap :=
      (le_div_iff₀ hgap).mpr (by dsimp only [gap]; nlinarith [estimate n x])
    _ = _ := by ring

end LeanShared.TwoNormSpectralShift
