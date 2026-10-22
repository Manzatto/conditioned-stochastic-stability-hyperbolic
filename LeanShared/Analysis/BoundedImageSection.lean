module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A quantitatively transverse image subspace has a constructed bounded
section of the actual endpoint projection. No invariance is required. -/
public noncomputable section
namespace LeanShared.BoundedImageSection
variable {U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem exists_section (B : U →L[ℝ] E) (Q : E →L[ℝ] U)
    (dimension : Module.finrank ℝ B.toLinearMap.range = Module.finrank ℝ U)
    {M : ℝ} (nonnegative : 0 ≤ M)
    (transverse : ∀ w : B.toLinearMap.range, ‖(w : E)‖ ≤ M * ‖Q w‖) :
    ∃ R : U →L[ℝ] E, ‖R‖ ≤ M ∧ B = R.comp (Q.comp B) := by
  let W := B.toLinearMap.range
  let P := Q.comp W.subtypeL
  have injective : Function.Injective P := by
    intro a b equal
    have zero : P (a-b) = 0 := by rw [map_sub, equal, sub_self]
    have normZero : ‖((a-b : W) : E)‖ = 0 := by
      apply le_antisymm _ (norm_nonneg _)
      simpa only [show Q ((a-b : W) : E) = 0 from zero, norm_zero, mul_zero] using transverse (a-b)
    exact sub_eq_zero.mp (Subtype.ext (norm_eq_zero.mp normZero))
  let e : W ≃L[ℝ] U :=
    (P.toLinearMap.linearEquivOfInjective injective dimension).toContinuousLinearEquiv
  let R := W.subtypeL.comp e.symm.toContinuousLinearMap
  have inverse (u : U) : Q (e.symm u : E) = u := e.apply_symm_apply u
  refine ⟨R, ContinuousLinearMap.opNorm_le_bound _ nonnegative ?_, ?_⟩
  · intro u
    exact (transverse (e.symm u)).trans_eq (by rw [inverse])
  · apply ContinuousLinearMap.ext
    intro u
    let w : W := ⟨B u, ⟨u, rfl⟩⟩
    have equal : (e.symm (e w) : E) = B u := congrArg Subtype.val (e.symm_apply_apply w)
    exact equal.symm
end LeanShared.BoundedImageSection
