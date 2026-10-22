module

public import LeanShared.Analysis.ConeDyadicSymbols
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Ring

/-!
# Finite telescoping and pointwise resolution of the actual cone symbols

Both sign branches and every radial dyadic factor are the constructed symbols
of `ConeDyadicSymbols`. Their partition of unity is proved, not assumed.
-/

@[expose] public noncomputable section

open Set Filter
open scoped SchwartzMap BigOperators Topology

namespace LeanShared.ConeDyadicResolution

open ConeDyadicSymbols

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {Cplus Cminus : Set E}
  (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus)

theorem inv_dyadic_succ (n : ℕ) :
    2 * ((2 : ℝ) ^ (n + 1))⁻¹ = ((2 : ℝ) ^ n)⁻¹ := by
  rw [pow_succ, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_mul]

theorem sum_signs_zero (ξ : E) : ∑ s : Bool, symbols χ Φ (0, s) ξ = (χ.toFun ‖ξ‖ : ℂ) := by
  rw [Fintype.sum_bool, symbols_apply_zero, symbols_apply_zero]
  ring

theorem sum_signs_succ (n : ℕ) (ξ : E) :
    (∑ s : Bool, symbols χ Φ (n + 1, s) ξ) =
      ((χ.toFun (((2 : ℝ) ^ (n + 1))⁻¹ * ‖ξ‖) -
        χ.toFun (((2 : ℝ) ^ n)⁻¹ * ‖ξ‖) : ℝ) : ℂ) := by
  rw [Fintype.sum_bool, symbols_apply_of_ne_zero χ Φ _ (Nat.succ_ne_zero _) ξ,
    symbols_apply_of_ne_zero χ Φ _ (Nat.succ_ne_zero _) ξ]
  simp only [angle, ↓reduceIte, Bool.false_eq_true, inv_dyadic_succ,
    Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- Exact finite two-sign partition: the remaining term is the outer radial cutoff. -/
theorem finite_sum (N : ℕ) (ξ : E) :
    (∑ n ∈ Finset.range (N + 1), ∑ s : Bool, symbols χ Φ (n, s) ξ) =
      (χ.toFun (((2 : ℝ) ^ N)⁻¹ * ‖ξ‖) : ℂ) := by
  induction N with
  | zero => simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      sum_signs_zero, pow_zero, inv_one, one_mul]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, sum_signs_succ]
      simp only [Complex.ofReal_sub]
      ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem tendsto_inv_dyadic_norm (ξ : E) :
    Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * ‖ξ‖) atTop (𝓝 0) := by
  simpa only [inv_pow, zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)).mul_const ‖ξ‖

/-- For every frequency the finite sum is eventually exactly one. -/
theorem eventually_finite_sum_eq_one (ξ : E) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.range (N + 1), ∑ s : Bool, symbols χ Φ (n, s) ξ) = 1 := by
  filter_upwards [(tendsto_inv_dyadic_norm ξ).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with N hN
  rw [finite_sum]
  have hn : 0 ≤ ((2 : ℝ) ^ N)⁻¹ * ‖ξ‖ := by positivity
  rw [χ.one _ (by simpa only [abs_of_nonneg hn] using hN.le), Complex.ofReal_one]

/-- At each fixed frequency only finitely many actual symbols are nonzero. -/
theorem eventually_symbols_eq_zero (ξ : E) :
    ∀ᶠ n : ℕ in atTop, ∀ s : Bool, symbols χ Φ (n, s) ξ = 0 := by
  filter_upwards [(tendsto_inv_dyadic_norm ξ).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)), eventually_gt_atTop (0 : ℕ)] with n hn hn0
  intro s
  rw [symbols_apply_of_ne_zero χ Φ _ (ne_of_gt hn0) ξ]
  have hp : 0 ≤ ((2 : ℝ) ^ n)⁻¹ * ‖ξ‖ := by positivity
  have h1 : χ.toFun (((2 : ℝ) ^ n)⁻¹ * ‖ξ‖) = 1 :=
    χ.one _ (by rw [abs_of_nonneg hp]; linarith)
  have h2 : χ.toFun ((2 * ((2 : ℝ) ^ n)⁻¹) * ‖ξ‖) = 1 := by
    apply χ.one
    rw [mul_assoc, abs_of_nonneg (mul_nonneg (by norm_num) hp)]
    linarith
  rw [h1, h2, sub_self, Complex.ofReal_zero, mul_zero]

/-- The actual double-indexed symbols have pointwise sum one, with finite support. -/
theorem hasSum_symbols (ξ : E) : HasSum (fun j : ℕ × Bool => symbols χ Φ j ξ) 1 := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((eventually_finite_sum_eq_one χ Φ ξ).and (eventually_symbols_eq_zero χ Φ ξ))
  let J : Finset (ℕ × Bool) := Finset.range (N + 1) ×ˢ Finset.univ
  have hz : ∀ j : ℕ × Bool, j ∉ J → symbols χ Φ j ξ = 0 := by
    intro j hj
    have hn : N + 1 ≤ j.1 := by
      simpa only [J, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true, not_lt] using hj
    exact (hN j.1 (Nat.le_trans (Nat.le_succ N) hn)).2 j.2
  have hs : HasSum (fun j : ℕ × Bool => symbols χ Φ j ξ) (∑ j ∈ J, symbols χ Φ j ξ) :=
    hasSum_sum_of_ne_finset_zero (s := J) hz
  have heq : (∑ j ∈ J, symbols χ Φ j ξ) = 1 := by
    change (∑ j ∈ Finset.range (N + 1) ×ˢ Finset.univ, symbols χ Φ j ξ) = 1
    rw [Finset.sum_product]
    exact (hN N le_rfl).1
  exact heq ▸ hs

theorem tsum_symbols (ξ : E) : (∑' j : ℕ × Bool, symbols χ Φ j ξ) = 1 :=
  (hasSum_symbols χ Φ ξ).tsum_eq

/-- Pointwise multiplier separation follows from the proved finite partition.
The argument map permits explicit changes of Fourier convention. -/
theorem eq_zero_of_symbol_products_zero (a : E → E) (f : E → ℂ)
    (hzero : ∀ j : ℕ × Bool, ∀ ξ : E, symbols χ Φ j (a ξ) * f ξ = 0) : f = 0 := by
  funext ξ
  obtain ⟨N, hN⟩ := (eventually_finite_sum_eq_one χ Φ (a ξ)).exists
  have hh := congrArg (fun z : ℂ => z * f ξ) hN
  simp only [Finset.sum_mul, hzero, Finset.sum_const_zero, one_mul] at hh
  exact hh.symm

end LeanShared.ConeDyadicResolution
