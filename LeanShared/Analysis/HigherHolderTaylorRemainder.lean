module
public import LeanShared.Analysis.HigherHolderIntegralRemainder
public import Mathlib.Tactic.Abel

/-! A genuine degree n+1 Taylor polynomial with its top coefficient written
as a universal scalar integral. The actual C^(n+1) derivative Holder bound
gives the fractional remainder, without another integer derivative. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LeanShared.HigherHolderTaylorRemainder
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

@[expose] def polynomial (f:E→F) (n:ℕ) (x y:E) : F :=
  (∑k∈Finset.range (n+1),(k.factorial:ℝ)⁻¹ • (iteratedFDeriv ℝ k f x (fun _=>y)))+
    (n.factorial:ℝ)⁻¹ • ((∫t in (0:ℝ)..1,(1-t)^n) •
      (iteratedFDeriv ℝ (n+1) f x (fun _=>y)))

theorem identity (f:E→F) (n:ℕ) (smooth:ContDiff ℝ (n+1) f) (x y:E) :
    f (x+y)-polynomial f n x y=(n.factorial:ℝ)⁻¹ •
      ∫t in (0:ℝ)..1,(1-t)^n •
        ((iteratedFDeriv ℝ (n+1) f (x+t•y)-iteratedFDeriv ℝ (n+1) f x) (fun _=>y)) := by
  have tensorContinuous:Continuous (fun t:ℝ=>iteratedFDeriv ℝ (n+1) f (x+t•y)):=
    (smooth.continuous_iteratedFDeriv (by rfl)).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have valueContinuous:Continuous (fun t:ℝ=>iteratedFDeriv ℝ (n+1) f (x+t•y) (fun _=>y)):=
    continuous_eval.comp (tensorContinuous.prodMk continuous_const)
  have weightContinuous:Continuous (fun t:ℝ=>(1-t)^n):=by fun_prop
  have integralIdentity:
      (∫t in (0:ℝ)..1,(1-t)^n •
        ((iteratedFDeriv ℝ (n+1) f (x+t•y)-iteratedFDeriv ℝ (n+1) f x) (fun _=>y)))=
      (∫t in (0:ℝ)..1,(1-t)^n • iteratedFDeriv ℝ (n+1) f (x+t•y) (fun _=>y))-
        (∫t in (0:ℝ)..1,(1-t)^n) • (iteratedFDeriv ℝ (n+1) f x (fun _=>y)):=by
    simp only [sub_apply,smul_sub]
    rw [intervalIntegral.integral_sub
      (f:=fun t:ℝ=>(1-t)^n • (iteratedFDeriv ℝ (n+1) f (x+t•y) (fun _=>y)))
      (g:=fun t:ℝ=>(1-t)^n • (iteratedFDeriv ℝ (n+1) f x (fun _=>y)))
      ((weightContinuous.smul valueContinuous).intervalIntegrable 0 1)
      ((weightContinuous.smul continuous_const).intervalIntegrable 0 1),
      intervalIntegral.integral_smul_const]
  rw [integralIdentity]
  have taylor:=map_add_eq_sum_add_integral_iteratedFDeriv (n:=n) (x:=x) (y:=y)
    (fun _ _=>smooth.contDiffAt)
  rw [taylor]
  dsimp only [polynomial]
  rw [smul_sub]
  abel

theorem bound (f:E→F) (n:ℕ) (smooth:ContDiff ℝ (n+1) f) {a C:ℝ} (ha:0≤a) (hC:0≤C)
    (holder:∀x z,‖iteratedFDeriv ℝ (n+1) f z-iteratedFDeriv ℝ (n+1) f x‖≤C*‖z-x‖^a)
    (x y:E) :
    ‖f (x+y)-polynomial f n x y‖≤|(n.factorial:ℝ)⁻¹| * C*‖y‖^(a+(n+1:ℕ)) := by
  rw [identity f n smooth x y,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (HigherHolderIntegralRemainder.bound f n ha hC holder x y)
    (abs_nonneg _)).trans_eq (mul_assoc _ _ _).symm
end LeanShared.HigherHolderTaylorRemainder
