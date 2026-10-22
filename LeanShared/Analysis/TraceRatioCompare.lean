module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! Normalized regularized traces that are relatively `η_j`-close to a positive sequence whose
normalization tends to one are eventually `2η_j`-close to the normalized sequence. -/
public section
open Filter
open scoped Topology
namespace LeanShared.TraceRatioCompare

theorem compare {ι : Type*} (τ : ι → ℕ → ℂ) (tr : ι → ℕ → ℝ) (L : ℕ → ℝ) (lam : ℝ)
    (lam_pos : 0 < lam) (p : ℕ → ℕ) (η : ι → ℝ) (hη : ∀ j, 0 ≤ η j)
    (expand : ∀ j k, τ j k = ((tr j (p k) / lam ^ p k : ℝ) : ℂ))
    (close : ∀ j k, |tr j (p k) - L (p k)| ≤ η j * L (p k))
    (ratio : Tendsto (fun k => L (p k) / lam ^ p k) atTop (𝓝 1)) :
    ∀ j, ∀ᶠ k in atTop, ‖τ j k - ((L (p k) / lam ^ p k : ℝ) : ℂ)‖ ≤ 2 * η j := by
  intro j
  filter_upwards [ratio.eventually (ge_mem_nhds (by norm_num : (1 : ℝ) < 2))] with k hk
  have pos := pow_pos lam_pos (p k)
  rw [expand, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← sub_div, abs_div,
    abs_of_pos pos]
  calc |tr j (p k) - L (p k)| / lam ^ p k ≤ η j * L (p k) / lam ^ p k :=
        div_le_div_of_nonneg_right (close j k) pos.le
    _ = η j * (L (p k) / lam ^ p k) := mul_div_assoc _ _ _
    _ ≤ η j * 2 := mul_le_mul_of_nonneg_left hk (hη j)
    _ = 2 * η j := mul_comm _ _

theorem periodic (L : ℕ → ℝ) (lam : ℝ) (p : ℕ → ℕ)
    (ratio : Tendsto (fun k => L (p k) / lam ^ p k) atTop (𝓝 1)) :
    Tendsto (fun k => ((L (p k) / lam ^ p k : ℝ) : ℂ)) atTop (𝓝 1) := by
  have := (Complex.continuous_ofReal.tendsto 1).comp ratio
  rw [Complex.ofReal_one] at this
  exact this

end LeanShared.TraceRatioCompare
