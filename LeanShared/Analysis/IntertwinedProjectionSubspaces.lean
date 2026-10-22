module
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-! A simultaneous projection intertwiner restricts to genuine equivalences
of BOTH splitting subspaces. The native norm and inverse norm bounds are
inherited without dimension or continuous-frame assumptions. -/
public noncomputable section
namespace LeanShared.IntertwinedProjectionSubspaces

variable {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

theorem range_map (P : H →L[ℝ] H) (Q : K →L[ℝ] K) (R : H ≃L[ℝ] K)
    (commutes : ∀ v, Q (R v) = R (P v)) : P.range.map R.toLinearMap = Q.range := by
  ext y
  constructor
  · rintro ⟨x,⟨v,hv⟩,rfl⟩
    refine ⟨R v,?_⟩
    change Q (R v) = R x
    rw [commutes]
    exact congrArg R hv
  · rintro ⟨v,rfl⟩
    refine ⟨P (R.symm v),⟨R.symm v,rfl⟩,?_⟩
    change R (P (R.symm v)) = Q v
    rw [← commutes,R.apply_symm_apply]

theorem kernel_map (P : H →L[ℝ] H) (Q : K →L[ℝ] K) (R : H ≃L[ℝ] K)
    (commutes : ∀ v, Q (R v) = R (P v)) : P.ker.map R.toLinearMap = Q.ker := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change Q (R x) = 0
    rw [commutes,show P x = 0 from hx,map_zero]
  · intro hy
    refine ⟨R.symm y,?_,R.apply_symm_apply y⟩
    change P (R.symm y) = 0
    apply R.injective
    rw [map_zero,← commutes,R.apply_symm_apply]
    exact hy

theorem restriction_norm_le (R : H ≃L[ℝ] K) (p : Submodule ℝ H) (q : Submodule ℝ K)
    (matched : p.map R.toLinearMap = q) :
    ‖(R.ofSubmodules p q matched).toContinuousLinearMap‖ ≤ ‖R.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖((R.ofSubmodules p q matched) v).val‖ ≤ ‖R.toContinuousLinearMap‖ * ‖v.val‖
  rw [ContinuousLinearEquiv.ofSubmodules_apply]
  exact R.toContinuousLinearMap.le_opNorm v.val

theorem restriction_inverse_norm_le (R : H ≃L[ℝ] K) (p : Submodule ℝ H) (q : Submodule ℝ K)
    (matched : p.map R.toLinearMap = q) :
    ‖(R.ofSubmodules p q matched).symm.toContinuousLinearMap‖ ≤ ‖R.symm.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖((R.ofSubmodules p q matched).symm v).val‖ ≤ ‖R.symm.toContinuousLinearMap‖ * ‖v.val‖
  rw [ContinuousLinearEquiv.ofSubmodules_symm_apply]
  exact R.symm.toContinuousLinearMap.le_opNorm v.val

end LeanShared.IntertwinedProjectionSubspaces
