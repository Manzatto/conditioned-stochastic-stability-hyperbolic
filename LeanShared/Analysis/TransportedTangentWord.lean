module

public import LeanShared.Analysis.FiniteDerivativeWord
public import LeanShared.Analysis.TangentVolumeJacobian
import Lean.Elab.Tactic.Omega

/-!
# Intrinsic Jacobian of a word on transported tangent fibers

The consecutive subspaces may change at every step. Each derivative is the
literal derivative of the corresponding random map at its actual prefix
state. Step invariance produces full-word invariance and multiplicativity of
the intrinsic tangent-volume factor. No common invariant noisy bundle and no
independently supplied scalar Jacobian cocycle are assumed.
-/

@[expose] public noncomputable section

open Set

namespace LeanShared.TransportedTangentWord

open CylinderPrincipalCoefficient FiniteDerivativeWord

variable {G E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [FiniteDimensional ℝ E] in
theorem prefixDerivative_mapsTo (F : G → E → E) {N : ℕ} (word : Fin N → G)
    (x : E) (U : ℕ → Submodule ℝ E)
    (hstep : ∀ k (hk : k < N), MapsTo
      (fderiv ℝ (F (word ⟨k, hk⟩)) (prefixOrbit F word k x)) (U k) (U (k + 1)))
    (k : ℕ) (hk : k ≤ N) : MapsTo (prefixDerivative F word x k) (U 0) (U k) := by
  induction k with
  | zero => exact fun _ hv => hv
  | succ k ih =>
    have hkN : k < N := by omega
    have hik : k ≤ N := Nat.le_of_succ_le hk
    intro v hv
    simp only [prefixDerivative, dite_eq_left hkN, ContinuousLinearMap.comp_apply]
    exact hstep k hkN (ih hik hv)

def tangentJacobianProduct (F : G → E → E) {N : ℕ} (word : Fin N → G)
    (x : E) (U : ℕ → Submodule ℝ E)
    (hstep : ∀ k (hk : k < N), MapsTo
      (fderiv ℝ (F (word ⟨k, hk⟩)) (prefixOrbit F word k x)) (U k) (U (k + 1))) : ℕ → ℝ
  | 0 => 1
  | k + 1 => if hk : k < N then
      (((fderiv ℝ (F (word ⟨k, hk⟩)) (prefixOrbit F word k x)).restrict
        (hstep k hk)).toLinearMap.normDet) * tangentJacobianProduct F word x U hstep k
    else tangentJacobianProduct F word x U hstep k

theorem normDet_prefixDerivative (F : G → E → E) {N : ℕ} (word : Fin N → G)
    (x : E) (U : ℕ → Submodule ℝ E) (e : ∀ k, H ≃ₗᵢ[ℝ] U k)
    (hstep : ∀ k (hk : k < N), MapsTo
      (fderiv ℝ (F (word ⟨k, hk⟩)) (prefixOrbit F word k x)) (U k) (U (k + 1)))
    (k : ℕ) (hk : k ≤ N) :
    ((prefixDerivative F word x k).restrict
      (prefixDerivative_mapsTo F word x U hstep k hk)).toLinearMap.normDet =
        tangentJacobianProduct F word x U hstep k := by
  induction k with
  | zero =>
    change (LinearMap.id : U 0 →ₗ[ℝ] U 0).normDet = 1
    exact LinearMap.normDet_id
  | succ k ih =>
    have hkN : k < N := by omega
    have hik : k ≤ N := Nat.le_of_succ_le hk
    simp only [tangentJacobianProduct, prefixDerivative, dite_eq_left hkN]
    change (((fderiv ℝ (F (word ⟨k, hkN⟩)) (prefixOrbit F word k x)).restrict
      (hstep k hkN)).toLinearMap.comp ((prefixDerivative F word x k).restrict
        (prefixDerivative_mapsTo F word x U hstep k hik)).toLinearMap).normDet = _
    rw [LinearMap.normDet_comp_of_finrank_eq _ _
      ((e 0).toLinearEquiv.finrank_eq.symm.trans (e k).toLinearEquiv.finrank_eq), ih hik]

def tangentNormProduct (F : G → E → E) {N : ℕ} (word : Fin N → G)
    (x : E) (U : ℕ → Submodule ℝ E)
    (hstep : ∀ k (hk : k < N), MapsTo
      (fderiv ℝ (F (word ⟨k, hk⟩)) (prefixOrbit F word k x)) (U k) (U (k + 1))) : ℕ → ℝ
  | 0 => 1
  | k + 1 => if hk : k < N then
      ‖(fderiv ℝ (F (word ⟨k, hk⟩)) (prefixOrbit F word k x)).restrict
        (hstep k hk)‖ * tangentNormProduct F word x U hstep k
    else tangentNormProduct F word x U hstep k

omit [FiniteDimensional ℝ E] in
/-- Genuine finite-word submultiplicativity of the intrinsic restricted
derivative norm, with transported fibers at each time. -/
theorem norm_prefixDerivative_le (F : G → E → E) {N : ℕ} (word : Fin N → G)
    (x : E) (U : ℕ → Submodule ℝ E)
    (hstep : ∀ k (hk : k < N), MapsTo
      (fderiv ℝ (F (word ⟨k, hk⟩)) (prefixOrbit F word k x)) (U k) (U (k + 1)))
    (k : ℕ) (hk : k ≤ N) :
    ‖(prefixDerivative F word x k).restrict
      (prefixDerivative_mapsTo F word x U hstep k hk)‖ ≤ tangentNormProduct F word x U hstep k := by
  induction k with
  | zero =>
    change ‖ContinuousLinearMap.id ℝ (U 0)‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    have hkN : k < N := by omega
    have hik : k ≤ N := Nat.le_of_succ_le hk
    simp only [tangentNormProduct, prefixDerivative, dite_eq_left hkN]
    change ‖((fderiv ℝ (F (word ⟨k, hkN⟩)) (prefixOrbit F word k x)).restrict
      (hstep k hkN)).comp ((prefixDerivative F word x k).restrict
        (prefixDerivative_mapsTo F word x U hstep k hik))‖ ≤ _
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (ih hik) (norm_nonneg _))

end LeanShared.TransportedTangentWord
