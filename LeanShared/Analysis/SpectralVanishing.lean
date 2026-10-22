module

public import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.NoncommRing

/-!
# Local finite extinction annihilates generalized eigenvectors

Only the observation functional annihilates one operator power. The whole
operator need not be nilpotent, and no decomposition into spatial blocks is
assumed. A nonzero scalar acts invertibly on every finite generalized
eigenspace, as proved here by induction on its Jordan order.
-/

@[expose] public noncomputable section

namespace LeanShared.SpectralVanishing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Local annihilation of `P^N` forces vanishing on every finite generalized
eigenspace with a nonzero eigenvalue, including complex generalized vectors. -/
theorem eval_generalized_eq_zero (P : E →L[𝕜] E) (ev : E →L[𝕜] 𝕜)
    {z : 𝕜} (hz : z ≠ 0) (N k : ℕ) (hlocal : ev.comp (P ^ N) = 0)
    (f : E) (hgen : ((P - z • 1) ^ k) f = 0) : ev f = 0 := by
  let Q := P - z • 1
  have hc : Commute Q P := by
    change (P - z • 1) * P = P * (P - z • 1)
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hann (u : E) : ev ((P ^ N) u) = 0 := by
    exact congrArg (fun A : E →L[𝕜] 𝕜 => A u) hlocal
  induction k generalizing f with
  | zero =>
      have hf : f = 0 := by simpa only [pow_zero, one_apply_eq_self] using hgen
      rw [hf, map_zero]
  | succ k ih =>
      have hQf : (Q ^ k) (Q f) = 0 := by
        change ((P - z • 1) ^ k) ((P - z • 1) f) = 0
        rw [← mul_apply_eq_comp, ← pow_succ]
        exact hgen
      have hvanish (j : ℕ) : ev ((P ^ j) (Q f)) = 0 := by
        apply ih
        change (Q ^ k) ((P ^ j) (Q f)) = 0
        rw [← mul_apply_eq_comp, (hc.pow_left k).pow_right j |>.eq,
          mul_apply_eq_comp, hQf, map_zero]
      have hrec (j : ℕ) : ev ((P ^ (j + 1)) f) = z * ev ((P ^ j) f) := by
        have hv := hvanish j
        have heq : (P ^ j) (Q f) = (P ^ (j + 1)) f - z • ((P ^ j) f) := by
          simp only [Q, sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul]
          rw [← mul_apply_eq_comp, ← pow_succ]
        rw [heq, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hv
        exact hv
      have hpow (j : ℕ) : ev ((P ^ j) f) = z ^ j * ev f := by
        induction j with
        | zero => simp
        | succ j ihj => rw [hrec, ihj, pow_succ']; simp only [mul_assoc]
      have hzval : z ^ N * ev f = 0 := by rw [← hpow N, hann]
      exact (mul_eq_zero.mp hzval).resolve_left (pow_ne_zero N hz)

/-- Ordinary eigenvectors are the order-one special case. -/
theorem eval_eigenvector_eq_zero (P : E →L[𝕜] E) (ev : E →L[𝕜] 𝕜)
    {z : 𝕜} (hz : z ≠ 0) (N : ℕ) (hlocal : ev.comp (P ^ N) = 0)
    (f : E) (heig : P f = z • f) : ev f = 0 := by
  apply eval_generalized_eq_zero P ev hz N 1 hlocal f
  simp only [pow_one, sub_apply, smul_apply, one_apply_eq_self, heig, sub_self]

end LeanShared.SpectralVanishing
