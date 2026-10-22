module
public import LeanShared.Analysis.BTLinkedDyadicRows

/-! Fractional nonstationary decay sums against the ACTUAL weakened
input exponents. The bound is uniform in output level and every finite
set of input levels; no count of dyadic blocks enters the constant. -/
public noncomputable section
open scoped BigOperators
namespace LeanShared.BTWeakDyadicRows
open BTLinkedDyadicWeights

theorem sign_row_bound (t s loss α:ℝ) (ht:0≤t) (hs:s≤0) (hLoss:0≤loss)
    (gap:t-s+loss<α) (n:ℕ) (σ τ:Bool) (J:Finset ℕ):
    ∑l∈J,(2:ℝ)^(exponent t s σ*n-(exponent t s τ-loss)*l-α*(max n l:ℕ))≤
      (1-(2:ℝ)^(-(α-(t-s+loss))))⁻¹:=by
  let β:=α-(t-s+loss)
  have hβ:0<β:=by dsimp only [β];linarith
  have out:exponent t s σ≤t:=by cases σ <;> dsimp only [exponent] <;> linarith
  have inp:s≤exponent t s τ:=by cases τ <;> dsimp only [exponent] <;> linarith
  have scalar (l:ℕ):exponent t s σ*n-(exponent t s τ-loss)*l-α*(max n l:ℕ)≤ -β*l:=by
    have nl:(n:ℝ)≤(max n l:ℕ):=by exact_mod_cast Nat.le_max_left n l
    have ll:(l:ℝ)≤(max n l:ℕ):=by exact_mod_cast Nat.le_max_right n l
    have a:=mul_le_mul_of_nonneg_right out (Nat.cast_nonneg n : (0:ℝ)≤n)
    have b:=mul_le_mul_of_nonneg_right inp (Nat.cast_nonneg l : (0:ℝ)≤l)
    have c:=mul_le_mul_of_nonneg_left nl ht
    have d:=mul_le_mul_of_nonneg_left ll (by linarith : 0≤loss-s)
    have e:=mul_le_mul_of_nonpos_left ll (neg_nonpos.mpr hβ.le)
    dsimp only [β] at e ⊢
    nlinarith
  have qn:0≤(2:ℝ)^(-β):=Real.rpow_nonneg (by norm_num) _
  have qs:(2:ℝ)^(-β)<1:=Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  calc
    _≤∑l∈J,((2:ℝ)^(-β))^l:=by
      apply Finset.sum_le_sum
      intro l _
      calc
        _≤(2:ℝ)^(-β*l):=Real.rpow_le_rpow_of_exponent_le (by norm_num) (scalar l)
        _=_:=by rw [Real.rpow_mul (by norm_num),Real.rpow_natCast]
    _≤∑'l:ℕ,((2:ℝ)^(-β))^l:=
      (summable_geometric_of_lt_one qn qs).sum_le_tsum _ (fun l _=>pow_nonneg qn l)
    _=_:=tsum_geometric_of_lt_one qn qs

theorem row_bound (t s loss α:ℝ) (ht:0≤t) (hs:s≤0) (hLoss:0≤loss)
    (gap:t-s+loss<α) (n:ℕ) (σ:Bool) (Jplus Jminus:Finset ℕ):
    (∑l∈Jplus,(2:ℝ)^(exponent t s σ*n-(t-loss)*l-α*(max n l:ℕ)))+
    (∑l∈Jminus,(2:ℝ)^(exponent t s σ*n-(s-loss)*l-α*(max n l:ℕ)))≤
      2*(1-(2:ℝ)^(-(α-(t-s+loss))))⁻¹:=by
  have plus:=sign_row_bound t s loss α ht hs hLoss gap n σ true Jplus
  have minus:=sign_row_bound t s loss α ht hs hLoss gap n σ false Jminus
  simp only [exponent] at plus minus ⊢
  linarith
end LeanShared.BTWeakDyadicRows
