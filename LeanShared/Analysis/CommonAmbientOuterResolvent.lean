module
public import LeanShared.Analysis.ResolventNeumannSeries
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! Common ambient actions identify the actual outer resolvents on matching
vectors. The ambient space need not be complete. -/
public noncomputable section
namespace LeanShared.CommonAmbientOuterResolvent
variable {E F Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem eq (P : E →L[ℂ] E) (Q : F →L[ℂ] F) (L : Z →L[ℂ] Z)
    (a : E →L[ℂ] Z) (b : F →L[ℂ] Z)
    (actionA : a.comp P = L.comp a) (actionB : b.comp Q = L.comp b)
    (x : E) (y : F) (common : a x = b y)
    (z : ℂ) (hP : ‖P‖ < ‖z‖) (hQ : ‖Q‖ < ‖z‖) :
    a ((resolvent P z) x) = b ((resolvent Q z) y) := by
  have terms (n : ℕ) : a (((z⁻¹ • P)^n) x) = b (((z⁻¹ • Q)^n) y) := by
    induction n with
    | zero => simpa only [pow_zero, one_apply_eq_self] using common
    | succ n ih =>
      simp only [pow_succ', mul_apply_eq_comp, smul_apply, map_smul]
      have hA := congrArg (fun T : E →L[ℂ] Z => T (((z⁻¹ • P)^n) x)) actionA
      have hB := congrArg (fun T : F →L[ℂ] Z => T (((z⁻¹ • Q)^n) y)) actionB
      change z⁻¹ • a (P (((z⁻¹ • P)^n) x)) = z⁻¹ • b (Q (((z⁻¹ • Q)^n) y))
      rw [show a (P (((z⁻¹ • P)^n) x)) = L (a (((z⁻¹ • P)^n) x)) from hA,
        show b (Q (((z⁻¹ • Q)^n) y)) = L (b (((z⁻¹ • Q)^n) y)) from hB, ih]
  have sumA := (ResolventNeumannSeries.hasSum P z hP).mapL
    (a.comp (ContinuousLinearMap.apply ℂ E x))
  have sumB := (ResolventNeumannSeries.hasSum Q z hQ).mapL
    (b.comp (ContinuousLinearMap.apply ℂ F y))
  apply sumA.unique
  convert sumB using 1
  · funext n
    change a ((z⁻¹ • ((z⁻¹ • P)^n)) x) = b ((z⁻¹ • ((z⁻¹ • Q)^n)) y)
    simp only [smul_apply, map_smul, terms n]
  · rfl
end LeanShared.CommonAmbientOuterResolvent
