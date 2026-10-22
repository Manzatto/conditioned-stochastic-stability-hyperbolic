module
public import LeanShared.Geometry.DiffeomorphismIterates
import Lean.Elab.Tactic.Omega

/-! Canonical backward-indexed bilateral orbits of actual homeomorphisms,
with exact forward/inverse integer times and N-step time conversion. -/
public section
namespace LeanShared.BilateralHomeomorphismOrbit
variable {X : Type*} [TopologicalSpace X]

@[expose] def orbit (F : X ≃ₜ X) (x : X) (n : ℤ) : X := (F^(-n)) x

@[simp] theorem zero (F : X ≃ₜ X) (x : X) : orbit F x 0=x := by simp [orbit]

theorem step (F : X ≃ₜ X) (x : X) (n : ℤ) : F (orbit F x (n+1))=orbit F x n := by
  change (F*F^(-(n+1))) x=(F^(-n)) x
  have exponent : (1:ℤ)+(-(n+1)) = -n := by omega
  calc
    (F*F^(-(n+1))) x = (F^(1:ℤ)*F^(-(n+1))) x := by rw [zpow_one]
    _ = (F^((1:ℤ)+(-(n+1)))) x := by rw [zpow_add]
    _ = (F^(-n)) x := by rw [exponent]

theorem nat_time (F : X ≃ₜ X) (x : X) (j : ℕ) :
    orbit F x (j:ℤ)=(F.symm : X → X)^[j] x := by
  rw [orbit,zpow_neg,zpow_natCast]
  exact congrFun (DiffeomorphismIterates.coe_symm_pow F j) x

theorem neg_nat_time (F : X ≃ₜ X) (x : X) (j : ℕ) :
    orbit F x (-(j:ℤ))=(F : X → X)^[j] x := by
  rw [orbit,neg_neg,zpow_natCast]
  exact congrFun (DiffeomorphismIterates.coe_pow F j) x

theorem pow_nat_time (T : X ≃ₜ X) (N : ℕ) (x : X) (j : ℕ) :
    orbit (T^N) x (j:ℤ)=(T.symm : X → X)^[N*j] x := by
  rw [orbit,zpow_neg,zpow_natCast,← pow_mul]
  exact congrFun (DiffeomorphismIterates.coe_symm_pow T (N*j)) x

theorem pow_neg_nat_time (T : X ≃ₜ X) (N : ℕ) (x : X) (j : ℕ) :
    orbit (T^N) x (-(j:ℤ))=(T : X → X)^[N*j] x := by
  rw [orbit,neg_neg,zpow_natCast,← pow_mul]
  exact congrFun (DiffeomorphismIterates.coe_pow T (N*j)) x

end LeanShared.BilateralHomeomorphismOrbit
