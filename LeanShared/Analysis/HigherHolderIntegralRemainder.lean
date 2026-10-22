module
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith

/-! The actual higher Taylor integral remainder gains the fractional Holder
order of the highest derivative. Only the available integer derivatives
are used; no ceiling-order derivative is assumed. -/
public noncomputable section
open Set MeasureTheory
namespace LeanShared.HigherHolderIntegralRemainder
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem bound (f:E→F) (n:ℕ) {a C:ℝ} (ha:0≤a) (hC:0≤C)
    (holder:∀x z,‖iteratedFDeriv ℝ (n+1) f z-iteratedFDeriv ℝ (n+1) f x‖≤C*‖z-x‖^a)
    (x y:E) :
    ‖∫ t in (0:ℝ)..1, (1-t)^n •
      ((iteratedFDeriv ℝ (n+1) f (x+t•y)-iteratedFDeriv ℝ (n+1) f x) (fun _=>y))‖≤
      C*‖y‖^(a+(n+1:ℕ)) := by
  have power:‖y‖^(a+(n+1:ℕ))=‖y‖^a*‖y‖^(n+1):=by
    rw [Real.rpow_add' (norm_nonneg _) (by positivity),Real.rpow_natCast]
  rw [power]
  have estimate:∀t∈Set.uIoc (0:ℝ) 1,
      ‖(1-t)^n • ((iteratedFDeriv ℝ (n+1) f (x+t•y)-iteratedFDeriv ℝ (n+1) f x) (fun _=>y))‖≤
        C*‖y‖^a*‖y‖^(n+1):=by
    intro t ht
    have ht':t∈Set.Ioc (0:ℝ) 1:=by simpa only [Set.uIoc_of_le zero_le_one] using ht
    have htn:0≤t:=ht'.1.le
    have displacement:‖x+t•y-x‖≤‖y‖:=by
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg htn]
      exact mul_le_of_le_one_left (norm_nonneg _) ht'.2
    have tensor:‖iteratedFDeriv ℝ (n+1) f (x+t•y)-iteratedFDeriv ℝ (n+1) f x‖≤C*‖y‖^a:=
      (holder x (x+t•y)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) displacement ha) hC)
    have value:= (iteratedFDeriv ℝ (n+1) f (x+t•y)-iteratedFDeriv ℝ (n+1) f x).le_opNorm (fun _=>y)
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at value
    have weight:‖(1-t)^n‖≤1:=by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (sub_nonneg.mpr ht'.2) _)]
      exact pow_le_one₀ (sub_nonneg.mpr ht'.2) (by linarith)
    rw [norm_smul]
    apply (mul_le_mul_of_nonneg_right weight (norm_nonneg _)).trans
    simpa only [one_mul] using (value.trans
      (mul_le_mul_of_nonneg_right tensor (pow_nonneg (norm_nonneg _) _)))
  have integral:=intervalIntegral.norm_integral_le_of_norm_le_const estimate
  simpa only [sub_zero,abs_one,mul_one,mul_assoc] using integral
end LeanShared.HigherHolderIntegralRemainder
