module
public import LeanShared.Analysis.DyadicSymbols
import Mathlib.Tactic

/-! Both low and high dyadic branches use a finite family of fixed
base multipliers; all scale and volume factors are exact. -/
public noncomputable section
open scoped SchwartzMap
namespace LeanShared.NormalizedDyadicKernel
variable {E S:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def base (low high:S→𝓢(E,ℂ)) (i:Bool × S):𝓢(E,ℂ):=
  if i.1 then high i.2 else low i.2

@[expose] def index (j:ℕ × S):Bool × S:=(decide (j.1≠0),j.2)

theorem kernel_identity (low high:S→𝓢(E,ℂ)) (j:ℕ × S) (x:E):
    DyadicSymbols.kernel low high j x=(((2:ℝ)^j.1)^Module.finrank ℝ E) •
      FourierSchwartzKernel.kernel (base low high (index j)) (((2:ℝ)^j.1) • x):=by
  by_cases hj:j.1=0
  · simp only [DyadicSymbols.kernel,DyadicSymbols.symbol,hj,↓reduceIte,
      index,base,ne_eq,not_true_eq_false,decide_false,pow_zero,one_pow,one_smul,Bool.false_eq_true]
  · simpa only [index,base,hj,ne_eq,not_false_eq_true,decide_true,↓reduceIte] using
      DyadicSymbols.kernel_apply_of_ne_zero low high j hj x

omit [MeasurableSpace E] [BorelSpace E] in
theorem symbol_normalization (low high:S→𝓢(E,ℂ)) (j:ℕ × S) (ξ:E):
    DyadicSymbols.symbol low high j (((2:ℝ)^j.1) • ξ)=base low high (index j) ξ:=by
  by_cases hj:j.1=0
  · simp [DyadicSymbols.symbol,index,base,hj]
  · rw [DyadicSymbols.symbol_apply_of_ne_zero low high j hj]
    simp [index,base,hj,inv_smul_smul₀ (pow_ne_zero _ (by norm_num : (2:ℝ)≠0))]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem base_compact (low high:S→𝓢(E,ℂ))
    (hl:∀s,HasCompactSupport (low s)) (hh:∀s,HasCompactSupport (high s)) (i:Bool × S):
    HasCompactSupport (base low high i):=by
  cases i with | mk b s=>cases b <;> simp only [base,Bool.false_eq_true,↓reduceIte] <;> first | exact hl s | exact hh s
end LeanShared.NormalizedDyadicKernel
