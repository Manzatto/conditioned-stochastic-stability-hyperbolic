module

public import LeanShared.Analysis.TransportedTangentWord
import Lean.Elab.Tactic.Omega

/-!
# Positive tangent-volume factors from actual inverse maps

Differentiating the literal inverse identity gives derivative injectivity.
Restriction to transported tangent fibers then has strictly positive
intrinsic volume factor, and the actual finite-word Jacobian product is
positive. No scalar positivity or Jacobian nonvanishing is an input.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace LeanShared.TangentDerivativePositivity

open CylinderPrincipalCoefficient FiniteDerivativeWord TransportedTangentWord

variable {G E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem restricted_normDet_pos_of_local_inverse (F B : E → E) (x : E)
    (U V : Submodule ℝ E) (hMaps : MapsTo (fderiv ℝ F x) U V)
    (hF : DifferentiableAt ℝ F x) (hB : DifferentiableAt ℝ B (F x))
    (hleft : ∀ᶠ y in 𝓝 x, B (F y) = y) :
    0 < ((fderiv ℝ F x).restrict hMaps).toLinearMap.normDet := by
  have hinj := fderiv_injective_of_local_inverse F B x hF hB hleft
  have hrestrict : Function.Injective ((fderiv ℝ F x).restrict hMaps).toLinearMap := by
    intro u v huv
    apply Subtype.ext
    exact hinj (congrArg Subtype.val huv)
  have hne := (((fderiv ℝ F x).restrict hMaps).toLinearMap.normDet_ne_zero_tfae.out 5 1).mp hrestrict
  exact lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm hne)

theorem tangentJacobianProduct_pos (F B : G → E → E)
    (hF : ∀ a, Differentiable ℝ (F a)) (hB : ∀ a, Differentiable ℝ (B a))
    (hleft : ∀ a x, B a (F a x) = x) {N : ℕ} (word : Fin N → G)
    (x : E) (U : ℕ → Submodule ℝ E)
    (hstep : ∀ k (hk : k < N), MapsTo
      (fderiv ℝ (F (word ⟨k, hk⟩)) (prefixOrbit F word k x)) (U k) (U (k + 1)))
    (k : ℕ) (hk : k ≤ N) : 0 < tangentJacobianProduct F word x U hstep k := by
  induction k with
  | zero => exact zero_lt_one
  | succ k ih =>
    have hkN : k < N := by omega
    simp only [tangentJacobianProduct, dite_eq_left hkN]
    apply mul_pos _ (ih (Nat.le_of_succ_le hk))
    exact restricted_normDet_pos_of_local_inverse (F (word ⟨k, hkN⟩)) (B (word ⟨k, hkN⟩))
      (prefixOrbit F word k x) (U k) (U (k + 1)) (hstep k hkN)
      (hF _ _) (hB _ _) (Eventually.of_forall (hleft _))

end LeanShared.TangentDerivativePositivity
