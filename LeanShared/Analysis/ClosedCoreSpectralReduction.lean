module

public import LeanShared.Analysis.DyadicCompletion
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! If a cutoff operator maps every continuous function into the closed
regular core, its nonzero generalized eigenvectors already lie there.
Restricting to that genuine Banach space preserves square compactness. -/

@[expose] public noncomputable section
open Set
namespace LeanShared.ClosedCoreSpectralReduction
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  (V : Submodule ℂ F) (Q : F →L[ℂ] F) (hQ : ∀ f, Q f ∈ V)

def operator : V →L[ℂ] V := Q.restrict (fun f _ => hQ f)

@[simp] theorem operator_coe (f : V) : (operator V Q hQ f : F) = Q f := rfl

include hQ in
theorem generalized_mem (z : ℂ) (hz : z ≠ 0) (k : ℕ) (f : F)
    (hf : ((Q - z • 1) ^ k) f = 0) : f ∈ V := by
  induction k generalizing f with
  | zero =>
    have : f = 0 := by simpa only [pow_zero, one_apply_eq_self] using hf
    rw [this]
    exact V.zero_mem
  | succ k ih =>
    have hstep : ((Q - z • 1) ^ k) ((Q - z • 1) f) = 0 := by
      simpa only [pow_succ, mul_apply_eq_comp] using hf
    have hs := ih _ hstep
    have hzmem : z • f ∈ V := by
      have hm := V.sub_mem (hQ f) hs
      convert hm using 1
      simp only [sub_apply, smul_apply, one_apply_eq_self, sub_sub_cancel]
    have hm := V.smul_mem z⁻¹ hzmem
    simpa only [smul_smul, inv_mul_cancel₀ hz, one_smul] using hm

theorem shift_power_coe (z : ℂ) (k : ℕ) (f : V) :
    (((operator V Q hQ - z • 1) ^ k) f : F) = ((Q - z • 1) ^ k) (f : F) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', mul_apply_eq_comp]
    change Q (((operator V Q hQ - z • 1) ^ k) f : F) -
      z • (((operator V Q hQ - z • 1) ^ k) f : F) = _
    rw [ih]
    rfl

theorem restricted_generalized (z : ℂ) (k : ℕ) (f : V)
    (hf : ((Q - z • 1) ^ k) (f : F) = 0) :
    ((operator V Q hQ - z • 1) ^ k) f = 0 := by
  apply Subtype.ext
  exact (shift_power_coe V Q hQ z k f).trans hf

theorem square_compact (hclosed : IsClosed (V : Set F))
    (hcompact : IsCompactOperator (Q ^ 2 : F →L[ℂ] F)) :
    IsCompactOperator (operator V Q hQ ^ 2 : V →L[ℂ] V) := by
  have hm : MapsTo (Q ^ 2 : F →L[ℂ] F) V V := fun f _ => hQ (Q f)
  have hc := hcompact.restrict hm hclosed
  convert hc using 1
  funext f
  apply Subtype.ext
  simp only [pow_two, mul_apply_eq_comp]
  rfl

end LeanShared.ClosedCoreSpectralReduction
