module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.FieldSimp

/-! The actual scalar eigenvalue of a commuting rank-one projection can be
read by any nonvanishing bounded scalar test. -/

public section
open ContinuousLinearMap
namespace LeanShared.RankOneCommutingEigenvalue
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A commuting normalized rank-one projection supplies its actual right
eigenvector and eigen-action; the scalar test need not be the rank-one mean. -/
theorem eigen_action (T P : E →L[ℂ] E) (ℓ ψ : E →L[ℂ] ℂ) (v : E)
    (factor : P = ℓ.smulRight v) (normalization : ℓ v = 1)
    (commutes : T * P = P * T) (nonzero : ψ v ≠ 0) :
    T v = (ψ (T v) / ψ v) • v ∧ T * P = (ψ (T v) / ψ v) • P := by
  have fixed : P v = v := by rw [factor, smulRight_apply, normalization, one_smul]
  have eigen : T v = ℓ (T v) • v := by
    calc
      T v = T (P v) := by rw [fixed]
      _ = P (T v) := congrArg (fun Q : E →L[ℂ] E => Q v) commutes
      _ = _ := by rw [factor, smulRight_apply]
  have scalar : ψ (T v) / ψ v = ℓ (T v) := by
    apply (div_eq_iff nonzero).mpr
    have hh := congrArg ψ eigen
    simpa only [map_smul, smul_eq_mul] using hh
  rw [scalar]
  refine ⟨eigen, ?_⟩
  rw [factor]
  ext x
  change T (ℓ x • v) = ℓ (T v) • (ℓ x • v)
  conv_lhs => rw [map_smul, eigen]
  simp only [smul_smul, mul_comm]

end LeanShared.RankOneCommutingEigenvalue
