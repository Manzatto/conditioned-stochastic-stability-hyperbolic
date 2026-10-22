module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! Exact algebra of shifted powers in a common ambient space. -/
public section
namespace LeanShared.CommonAmbientShiftPowers
variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem map (P : E →L[ℂ] E) (L : Z →L[ℂ] Z) (a : E →L[ℂ] Z)
    (action : a.comp P = L.comp a) (z : ℂ) (n : ℕ) (x : E) :
    a (((P-z•1)^n) x) = ((L-z•1)^n) (a x) := by
  have shift (v : E) : a ((P-z•1) v) = (L-z•1) (a v) := by
    have commute := congrArg (fun T : E →L[ℂ] Z => T v) action
    simpa only [sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul,
      ContinuousLinearMap.comp_apply] using congrArg (fun w => w-z•a v) commute
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ n ih =>
    simp only [pow_succ',mul_apply_eq_comp,shift,ih]

theorem kernel_mem_of_match {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (P : E →L[ℂ] E) (Q : F →L[ℂ] F) (L : Z →L[ℂ] Z)
    (a : E →L[ℂ] Z) (b : F →L[ℂ] Z)
    (actionA : a.comp P = L.comp a) (actionB : b.comp Q = L.comp b)
    (injectiveB : Function.Injective b) (z : ℂ) (n : ℕ) (x : E) (y : F)
    (common : a x = b y) (kernel : ((P-z•1)^n) x = 0) : ((Q-z•1)^n) y = 0 := by
  apply injectiveB
  rw [map_zero,map Q L b actionB,←common,←map P L a actionA,kernel,map_zero]
end LeanShared.CommonAmbientShiftPowers
