module
public import LeanShared.Analysis.BTLinkedDyadicWeights
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! Uniform resonant dyadic row sums for the literal BT linked relation.
The constants depend only on the exponents, not the word or integer
thresholds. Integer shifts reindex actual geometric series injectively. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.BTLinkedDyadicWeights

instance linked_decidable (hplus hminus : ℤ) (output input : ℕ × Bool) :
    Decidable (linked hplus hminus output input) := by
  unfold linked
  infer_instance

private theorem shifted_sum (J : Finset ℕ) (k : ℕ → ℕ)
    (injective : Set.InjOn k (J : Set ℕ)) (q b : ℝ) (negative : q < 0)
    (e : ℕ → ℝ) (bound : ∀ l ∈ J, e l ≤ b + q * (k l : ℝ)) :
    ∑ l ∈ J, (2 : ℝ) ^ e l ≤ (2 : ℝ) ^ b * (1 - (2 : ℝ)^q)⁻¹ := by
  classical
  have qnonnegative : 0 ≤ (2 : ℝ)^q := Real.rpow_nonneg (by norm_num) _
  have qsmall : (2 : ℝ)^q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) negative
  have geometric : ∑ l ∈ J, ((2 : ℝ)^q)^(k l) ≤ (1-(2 : ℝ)^q)⁻¹ := by
    calc
      _ = ∑ j ∈ J.image k, ((2 : ℝ)^q)^j := (Finset.sum_image (by
        intro l hl m hm same
        exact injective hl hm same)).symm
      _ ≤ ∑' j : ℕ, ((2 : ℝ)^q)^j :=
        (summable_geometric_of_lt_one qnonnegative qsmall).sum_le_tsum _
          (fun j _ => pow_nonneg qnonnegative j)
      _ = _ := tsum_geometric_of_lt_one qnonnegative qsmall
  calc
    _ ≤ ∑ l ∈ J, (2 : ℝ)^b * ((2 : ℝ)^q)^(k l) := by
      apply Finset.sum_le_sum
      intro l hl
      calc
        _ ≤ (2 : ℝ)^(b+q*(k l : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (bound l hl)
        _ = _ := by rw [Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num) q (k l : ℝ), Real.rpow_natCast]
    _ = (2 : ℝ)^b * ∑ l ∈ J, ((2 : ℝ)^q)^(k l) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left geometric (Real.rpow_nonneg (by norm_num) _)

theorem plus_row (t : ℝ) (positive : 0 < t) (hplus : ℤ) (n : ℕ) (J : Finset ℕ)
    (levels : ∀ l ∈ J, (n : ℤ) ≤ (l : ℤ) + hplus) :
    ∑ l ∈ J, (2 : ℝ)^(t*n-t*l) ≤ (2 : ℝ)^(t*hplus) * (1-(2 : ℝ)^(-t))⁻¹ := by
  let k : ℕ → ℕ := fun l => ((l : ℤ)+hplus-(n : ℤ)).toNat
  have integer (l : ℕ) (hl : l ∈ J) : (k l : ℤ) = (l : ℤ)+hplus-(n : ℤ) :=
    Int.toNat_of_nonneg (by have h := levels l hl; linarith)
  refine shifted_sum J k ?_ (-t) (t*hplus) (neg_neg_of_pos positive) (fun l => t*n-t*l) ?_
  · intro l hl m hm same
    have equal : (k l : ℤ) = (k m : ℤ) := congrArg (fun j : ℕ => (j : ℤ)) same
    have : (l : ℤ) = (m : ℤ) := by rw [integer l hl, integer m hm] at equal; linarith
    exact_mod_cast this
  · intro l hl
    have real : (k l : ℝ) = (l : ℝ)+(hplus : ℝ)-(n : ℝ) := by exact_mod_cast integer l hl
    nlinarith

theorem minus_row (s : ℝ) (negative : s < 0) (hminus : ℤ) (n : ℕ) (J : Finset ℕ)
    (levels : ∀ l ∈ J, (l : ℤ)+hminus ≤ (n : ℤ)) :
    ∑ l ∈ J, (2 : ℝ)^(s*n-s*l) ≤ (2 : ℝ)^(s*hminus) * (1-(2 : ℝ)^s)⁻¹ := by
  let k : ℕ → ℕ := fun l => ((n : ℤ)-(l : ℤ)-hminus).toNat
  have integer (l : ℕ) (hl : l ∈ J) : (k l : ℤ) = (n : ℤ)-(l : ℤ)-hminus :=
    Int.toNat_of_nonneg (by have h := levels l hl; linarith)
  refine shifted_sum J k ?_ s (s*hminus) negative (fun l => s*n-s*l) ?_
  · intro l hl m hm same
    have equal : (k l : ℤ) = (k m : ℤ) := congrArg (fun j : ℕ => (j : ℤ)) same
    have : (l : ℤ) = (m : ℤ) := by rw [integer l hl, integer m hm] at equal; linarith
    exact_mod_cast this
  · intro l hl
    have real : (k l : ℝ) = (n : ℝ)-(l : ℝ)-(hminus : ℝ) := by exact_mod_cast integer l hl
    nlinarith
theorem mixed_row (t s : ℝ) (ht : 0 < t) (hs : s ≤ 0)
    (hplus hminus : ℤ) (n : ℕ) (J : Finset ℕ)
    (levels : ∀ l ∈ J, hminus ≤ (n : ℤ) ∨ -hplus ≤ (l : ℤ)) :
    ∑ l ∈ J, (2 : ℝ)^(s*n-t*l) ≤
      max ((2 : ℝ)^(t*hplus)) ((2 : ℝ)^(s*hminus)) * (1-(2 : ℝ)^(-t))⁻¹ := by
  have small : (2 : ℝ)^(-t) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht)
  have denominator : 0 ≤ (1-(2 : ℝ)^(-t))⁻¹ := inv_nonneg.mpr (sub_pos.mpr small).le
  by_cases hn : hminus ≤ (n : ℤ)
  · have sumBound : ∑ l ∈ J, (2 : ℝ)^(s*n-t*l) ≤
        (2 : ℝ)^(s*hminus) * (1-(2 : ℝ)^(-t))⁻¹ := by
      refine shifted_sum J id (fun _ _ _ _ same => same) (-t) (s*hminus)
        (neg_neg_of_pos ht) (fun l => s*n-t*l) ?_
      intro l _hl
      have real : (hminus : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have estimate := mul_le_mul_of_nonpos_left real hs
      simpa only [id_eq] using (show s*(n : ℝ)-t*l ≤ s*hminus+(-t)*(l : ℝ) by nlinarith)
    exact sumBound.trans (mul_le_mul_of_nonneg_right (le_max_right ((2 : ℝ)^(t*hplus)) ((2 : ℝ)^(s*hminus))) denominator)
  · let k : ℕ → ℕ := fun l => ((l : ℤ)+hplus).toNat
    have integer (l : ℕ) (hl : l ∈ J) : (k l : ℤ) = (l : ℤ)+hplus :=
      Int.toNat_of_nonneg (by have h := (levels l hl).resolve_left hn; linarith)
    have sumBound : ∑ l ∈ J, (2 : ℝ)^(s*n-t*l) ≤
        (2 : ℝ)^(t*hplus) * (1-(2 : ℝ)^(-t))⁻¹ := by
      refine shifted_sum J k ?_ (-t) (t*hplus) (neg_neg_of_pos ht) (fun l => s*n-t*l) ?_
      · intro l hl m hm same
        have equal : (k l : ℤ) = (k m : ℤ) := congrArg (fun j : ℕ => (j : ℤ)) same
        have : (l : ℤ) = (m : ℤ) := by rw [integer l hl, integer m hm] at equal; linarith
        exact_mod_cast this
      · intro l hl
        have real : (k l : ℝ) = (l : ℝ)+(hplus : ℝ) := by exact_mod_cast integer l hl
        have nonpositive := mul_nonpos_of_nonpos_of_nonneg hs (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        nlinarith
    exact sumBound.trans (mul_le_mul_of_nonneg_right (le_max_left ((2 : ℝ)^(t*hplus)) ((2 : ℝ)^(s*hminus))) denominator)

@[expose] def rowConstant (t s : ℝ) : ℝ := (1-(2 : ℝ)^(-t))⁻¹ + (1-(2 : ℝ)^s)⁻¹

theorem rowConstant_positive (t s : ℝ) (ht : 0 < t) (hs : s < 0) : 0 < rowConstant t s := by
  exact add_pos (inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht))))
    (inv_pos.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hs)))

/-- Every finite linked row has a uniform sum. Both signs are summed, and
neither integer thresholds nor their signs enter the structural constant. -/
theorem row_bound (t s : ℝ) (ht : 0 < t) (hs : s < 0)
    (hplus hminus : ℤ) (output : ℕ × Bool) (J : Finset ℕ) :
    (∑ l ∈ J.filter (fun l => linked hplus hminus output (l,true)),
      (2 : ℝ)^(exponent t s output.2*output.1-t*l)) +
    (∑ l ∈ J.filter (fun l => linked hplus hminus output (l,false)),
      (2 : ℝ)^(exponent t s output.2*output.1-s*l)) ≤
      max ((2 : ℝ)^(t*hplus)) ((2 : ℝ)^(s*hminus)) * rowConstant t s := by
  classical
  rcases output with ⟨n, sign⟩
  let P := max ((2 : ℝ)^(t*hplus)) ((2 : ℝ)^(s*hminus))
  cases sign
  · let Jp := J.filter (fun l => linked hplus hminus (n,false) (l,true))
    let Jm := J.filter (fun l => linked hplus hminus (n,false) (l,false))
    have first := mixed_row t s ht hs.le hplus hminus n Jp (by
      intro l hl
      simpa only [linked, Bool.false_eq_true, Bool.true_eq_false, and_false, false_and,
        true_and, false_or, or_false] using (Finset.mem_filter.mp hl).2)
    have second := minus_row s hs hminus n Jm (by
      intro l hl
      simpa only [linked, Bool.false_eq_true, Bool.true_eq_false, and_false, false_and,
        true_and, false_or, or_false] using (Finset.mem_filter.mp hl).2)
    have denominator : 0 ≤ (1-(2 : ℝ)^s)⁻¹ :=
      inv_nonneg.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hs)).le
    have second' := second.trans (mul_le_mul_of_nonneg_right (le_max_right ((2 : ℝ)^(t*hplus)) ((2 : ℝ)^(s*hminus))) denominator)
    change (∑ l ∈ Jp, (2 : ℝ)^(s*n-t*l)) + (∑ l ∈ Jm, (2 : ℝ)^(s*n-s*l)) ≤ P * rowConstant t s
    exact (add_le_add first second').trans_eq (by dsimp only [rowConstant, P]; ring)
  · let Jp := J.filter (fun l => linked hplus hminus (n,true) (l,true))
    have empty : J.filter (fun l => linked hplus hminus (n,true) (l,false)) = ∅ := by simp [linked]
    rw [empty, Finset.sum_empty, add_zero]
    have first := plus_row t ht hplus n Jp (by
      intro l hl
      simpa only [linked, Bool.false_eq_true, Bool.true_eq_false, and_false, false_and,
        true_and, false_or, or_false] using (Finset.mem_filter.mp hl).2)
    have denominatorP : 0 ≤ (1-(2 : ℝ)^(-t))⁻¹ := inv_nonneg.mpr
      (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht))).le
    have denominatorM : 0 ≤ (1-(2 : ℝ)^s)⁻¹ :=
      inv_nonneg.mpr (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hs)).le
    have nonnegativeP : 0 ≤ P := (Real.rpow_nonneg (by norm_num) _).trans (le_max_left ((2 : ℝ)^(t*hplus)) ((2 : ℝ)^(s*hminus)))
    change (∑ l ∈ Jp, (2 : ℝ)^(t*n-t*l)) ≤ P * rowConstant t s
    exact first.trans ((mul_le_mul_of_nonneg_right (le_max_left ((2 : ℝ)^(t*hplus)) ((2 : ℝ)^(s*hminus))) denominatorP).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right denominatorM) nonnegativeP))
end LeanShared.BTLinkedDyadicWeights
