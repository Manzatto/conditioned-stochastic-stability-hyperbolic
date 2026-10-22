module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! The pressure supporting inequality from Jensen. If positive normalized orbit masses `Z n` tend
to `a > 0`, the averaged Birkhoff masses `B n / n` tend to `a ν`, Jensen gives `t B n ≤ Z n (log
Z_t n - log Z n)`, and the tilted masses grow like `R^n` for every `R > e^c`, then `t ν ≤ c`. -/
public section
open Filter Real
open scoped Topology
namespace LeanShared.JensenPressureTangent

theorem tangent_of_jensen (Z Zt B : ℕ → ℝ) (a ν t c : ℝ) (ha : 0 < a)
    (hZ : Tendsto Z atTop (𝓝 a)) (hB : Tendsto (fun n => B n / n) atTop (𝓝 (a * ν)))
    (hZt : ∀ᶠ n in atTop, 0 < Zt n)
    (jensen : ∀ᶠ n in atTop, t * B n ≤ Z n * (log (Zt n) - log (Z n)))
    (growth : ∀ R, exp c < R → ∃ C, ∀ n, Zt n ≤ C * R ^ n) : t * ν ≤ c := by
  have bound : ∀ R, exp c < R → t * ν ≤ log R := by
    intro R hR
    have Rpos : 0 < R := (exp_pos c).trans hR
    obtain ⟨C, hC⟩ := growth R hR
    have Cpos : 0 < C := by
      obtain ⟨n0, hn0⟩ := hZt.exists
      have := hn0.trans_le (hC n0)
      exact pos_of_mul_pos_left this (pow_pos Rpos n0).le
    have left : Tendsto (fun n => t * (B n / n)) atTop (𝓝 (t * (a * ν))) := hB.const_mul t
    have logZ : Tendsto (fun n => log C - log (Z n)) atTop (𝓝 (log C - log a)) :=
      tendsto_const_nhds.sub ((continuousAt_log ha.ne').tendsto.comp hZ)
    have vanish : Tendsto (fun n : ℕ => (log C - log (Z n)) / n) atTop (𝓝 0) :=
      logZ.div_atTop tendsto_natCast_atTop_atTop
    have right : Tendsto (fun n : ℕ => Z n * ((log C - log (Z n)) / n + log R)) atTop
        (𝓝 (a * (0 + log R))) := hZ.mul (vanish.add tendsto_const_nhds)
    have eventually : ∀ᶠ n : ℕ in atTop,
        t * (B n / n) ≤ Z n * ((log C - log (Z n)) / n + log R) := by
      filter_upwards [jensen, hZ.eventually (lt_mem_nhds ha), eventually_gt_atTop 0, hZt]
        with n hj hz hn hzt
      have npos : (0 : ℝ) < n := by exact_mod_cast hn
      have logBound : log (Zt n) ≤ log C + n * log R := by
        calc log (Zt n) ≤ log (C * R ^ n) := log_le_log hzt (hC n)
          _ = log C + n * log R := by
            rw [log_mul Cpos.ne' (pow_pos Rpos n).ne', log_pow]
      have step : t * B n ≤ Z n * (log C + n * log R - log (Z n)) :=
        hj.trans (mul_le_mul_of_nonneg_left (by linarith) hz.le)
      have expand : Z n * ((log C - log (Z n)) / n + log R) =
          Z n * (log C + n * log R - log (Z n)) / n := by
        field_simp
        ring
      rw [expand, le_div_iff₀ npos]
      have cancel : t * (B n / n) * n = t * B n := by field_simp
      rw [cancel]
      exact step
    have limit := le_of_tendsto_of_tendsto left right eventually
    rw [zero_add] at limit
    have : a * (t * ν) ≤ a * log R := by linarith
    exact le_of_mul_le_mul_left this ha
  by_contra h
  push Not at h
  have := bound (exp ((c + t * ν) / 2)) (exp_lt_exp.mpr (by linarith))
  rw [log_exp] at this
  linarith

end LeanShared.JensenPressureTangent
