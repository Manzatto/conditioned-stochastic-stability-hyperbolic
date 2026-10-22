module

public import LeanShared.Analysis.GraphBlockStableEstimate
public import LeanShared.Analysis.PerturbedLinearEquivalence

/-! The forward graph transform is constructed for every actual small
perturbation of a contracting/expanding diagonal block. -/
public noncomputable section
namespace LeanShared.HyperbolicForwardGraphStep
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
open GraphBlockPerturbation

theorem exists_step (A : U ≃L[ℝ] U) (B : S →L[ℝ] S)
    (L : U × S →L[ℝ] U × S) (G : U →L[ℝ] S)
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ 1 / 4) (hB : ‖B‖ ≤ 1 / 4)
    (hG : ‖G‖ ≤ 1) (η : ℝ) (small : η ≤ 1 / 16)
    (close : ‖L - A.toContinuousLinearMap.prodMap B‖ ≤ η) :
    ∃ C : U ≃L[ℝ] U, ∃ H : U →L[ℝ] S,
      C.toContinuousLinearMap = upper L G ∧ ‖C.symm.toContinuousLinearMap‖ ≤ 1 / 2 ∧
      ‖H‖ ≤ 1 ∧ L.comp (graph G) = (graph H).comp C.toContinuousLinearMap := by
  have positive : 0 ≤ η := (norm_nonneg _).trans close
  have error := upper_error A.toContinuousLinearMap B L G hG η close
  have normalized : ‖A.symm.toContinuousLinearMap.comp (upper L G - A.toContinuousLinearMap)‖ ≤ 1 / 2 := by
    calc
      _ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖upper L G - A.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 / 4) * η := mul_le_mul hA error (norm_nonneg _) (by norm_num)
      _ ≤ 1 / 2 := by linarith
  obtain ⟨C, actual, inverse⟩ := PerturbedLinearEquivalence.exists_equivalence A (upper L G)
    (1 / 2) (by norm_num) normalized
  have inverseBound : ‖C.symm.toContinuousLinearMap‖ ≤ 1 / 2 := by
    have bound : (1 / (1 - (1 / 2 : ℝ))) * ‖A.symm.toContinuousLinearMap‖ ≤ 1 / 2 := by
      norm_num
      linarith
    exact inverse.trans bound
  have lowerBound : ‖lower L G‖ ≤ 1 := by
    have estimate := lower_norm_le A.toContinuousLinearMap B L G hG η close
    have productBound := mul_le_mul hB hG (norm_nonneg G) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith
  let H := (lower L G).comp C.symm.toContinuousLinearMap
  have graphBound : ‖H‖ ≤ 1 := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul lowerBound inverseBound (norm_nonneg _) zero_le_one).trans (by norm_num))
  refine ⟨C, H, actual, inverseBound, graphBound, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · exact (congrArg (fun F : U →L[ℝ] U => F v) actual).symm
  · change (L (v, G v)).2 = lower L G (C.symm (C v))
    rw [C.symm_apply_apply]
    rfl

end LeanShared.HyperbolicForwardGraphStep
