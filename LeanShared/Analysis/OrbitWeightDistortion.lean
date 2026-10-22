module

public import LeanShared.Analysis.CylinderPrincipalCoefficient
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positive-envelope distortion along actual orbit cylinders

The selected pressure density needs bounded distortion, not a separate
supremum comparison assumed as a scalar inequality. A Hölder bound for
the logarithm of the fixed positive envelope and a summable cylinder
orbit-distance bound give the accumulated-weight ratio directly.
The orbit-distance summability is the precise hyperbolic geometric input;
the unstable-Jacobian logarithm has an analogous classical distortion input.
-/

@[expose] public noncomputable section

open Set
open scoped BigOperators

namespace LeanShared.OrbitWeightDistortion

open CylinderPrincipalCoefficient

theorem log_sub_le_of_lower_bound (a b m : ℝ) (hm : 0 < m)
    (ha : m ≤ a) (hb : m ≤ b) : Real.log a - Real.log b ≤ |a - b| / m := by
  have ha0 := hm.trans_le ha
  have hb0 := hm.trans_le hb
  calc
    _ = Real.log (a / b) := (Real.log_div ha0.ne' hb0.ne').symm
    _ ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    _ = (a - b) / b := by rw [sub_div, div_self hb0.ne']
    _ ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb0.le
    _ ≤ _ := div_le_div_of_nonneg_left (abs_nonneg _) hm hb

theorem abs_log_sub_le_of_lower_bound (a b m : ℝ) (hm : 0 < m)
    (ha : m ≤ a) (hb : m ≤ b) : |Real.log a - Real.log b| ≤ |a - b| / m := by
  apply abs_le.mpr
  constructor
  · have h := log_sub_le_of_lower_bound b a m hm hb ha
    rw [abs_sub_comm] at h
    linarith
  · exact log_sub_le_of_lower_bound a b m hm ha hb

theorem product_le_of_log_errors {I : Type*} [Fintype I]
    (a b e : I → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (herr : ∀ i, |Real.log (a i) - Real.log (b i)| ≤ e i)
    (B : ℝ) (hsum : (∑ i, e i) ≤ B) :
    (∏ i, a i) ≤ Real.exp B * ∏ i, b i := by
  have hlogs : (∑ i, Real.log (a i)) ≤ B + ∑ i, Real.log (b i) := by
    have hdiff : (∑ i, (Real.log (a i) - Real.log (b i))) ≤ B :=
      (Finset.sum_le_sum fun i _ => (le_abs_self _).trans (herr i)).trans hsum
    rw [Finset.sum_sub_distrib] at hdiff
    linarith
  have hexp := Real.exp_le_exp.mpr hlogs
  rw [Real.exp_add, Real.exp_sum, Real.exp_sum] at hexp
  simpa only [Real.exp_log (ha _), Real.exp_log (hb _)] using hexp

theorem actual_wordWeight_le {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    (F : G → X → X) (g : X → ℝ) {N : ℕ} (word : Fin N → G) (x z : X)
    (e : Fin N → ℝ) (H B : ℝ) (hH : 0 ≤ H)
    (hpositive : ∀ j : Fin N,
      0 < g (prefixOrbit F word j.val x) ∧ 0 < g (prefixOrbit F word j.val z))
    (hlog : ∀ j : Fin N,
      |Real.log (g (prefixOrbit F word j.val x)) -
        Real.log (g (prefixOrbit F word j.val z))| ≤ H * e j)
    (hsum : (∑ j, e j) ≤ B) :
    wordWeight F g (word, x) ≤ Real.exp (H * B) * wordWeight F g (word, z) := by
  have h := product_le_of_log_errors
    (fun j : Fin N => g (prefixOrbit F word j.val x))
    (fun j : Fin N => g (prefixOrbit F word j.val z))
    (fun j => H * e j) (fun j => (hpositive j).1) (fun j => (hpositive j).2) hlog
    (H * B) (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hsum hH)
  have hx : ∀ j : Fin N, |g (prefixOrbit F word j.val x)| = g (prefixOrbit F word j.val x) :=
    fun j => abs_of_pos (hpositive j).1
  have hz : ∀ j : Fin N, |g (prefixOrbit F word j.val z)| = g (prefixOrbit F word j.val z) :=
    fun j => abs_of_pos (hpositive j).2
  simpa only [wordWeight, hx, hz] using h

theorem positive_envelope_wordWeight_le {X G : Type*}
    [TopologicalSpace X] [TopologicalSpace G]
    (F : G → X → X) (g : X → ℝ) {N : ℕ} (word : Fin N → G) (x z : X)
    (e : Fin N → ℝ) (H B δ : ℝ) (hH : 0 ≤ H) (hδ : 0 < δ)
    (hg : ∀ j : Fin N,
      0 ≤ g (prefixOrbit F word j.val x) ∧ 0 ≤ g (prefixOrbit F word j.val z))
    (hdiff : ∀ j : Fin N,
      |g (prefixOrbit F word j.val x) - g (prefixOrbit F word j.val z)| ≤ H * e j)
    (hsum : (∑ j, e j) ≤ B) :
    wordWeight F (fun y => g y + δ) (word, x) ≤
      Real.exp ((H / δ) * B) * wordWeight F (fun y => g y + δ) (word, z) := by
  apply actual_wordWeight_le F (fun y => g y + δ) word x z e (H / δ) B
    (div_nonneg hH hδ.le) _ _ hsum
  · intro j
    exact ⟨add_pos_of_nonneg_of_pos (hg j).1 hδ,
      add_pos_of_nonneg_of_pos (hg j).2 hδ⟩
  · intro j
    have h := abs_log_sub_le_of_lower_bound
      (g (prefixOrbit F word j.val x) + δ) (g (prefixOrbit F word j.val z) + δ) δ hδ
      (le_add_of_nonneg_left (hg j).1) (le_add_of_nonneg_left (hg j).2)
    simp only [add_sub_add_right_eq_sub] at h
    calc
      _ ≤ _ := h
      _ ≤ (H * e j) / δ := div_le_div_of_nonneg_right (hdiff j) hδ.le
      _ = _ := by ring

end LeanShared.OrbitWeightDistortion
