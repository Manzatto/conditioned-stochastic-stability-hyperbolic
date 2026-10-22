module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! The logarithm of the actual Euclidean volume expansion is smooth at
every injective linear map, including zero-dimensional source spaces.
The proof uses the genuine Gram determinant and hence applies to moving
subspaces described by local frames. -/
public noncomputable section
namespace LeanShared.LogNormDetRegularity
open scoped ContDiff
variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

@[expose] def gramDet (A : U →L[ℝ] V) : ℝ :=
  (Matrix.gram ℝ (fun i => A (stdOrthonormalBasis ℝ U i))).det

theorem gramDet_eq (A : U →L[ℝ] V) : gramDet A = A.toLinearMap.normDet ^ 2 :=
  (A.toLinearMap.normDet_sq_eq_det_gram (stdOrthonormalBasis ℝ U)).symm

theorem contDiff_gramDet : ContDiff ℝ ∞ (gramDet (U := U) (V := V)) := by
  unfold gramDet
  simp only [Matrix.det_apply', Matrix.gram_apply]
  apply ContDiff.sum
  intro σ _
  apply ContDiff.mul contDiff_const
  apply contDiff_prod
  intro i _
  apply ContDiff.inner
  · exact contDiff_id.clm_apply contDiff_const
  · exact contDiff_id.clm_apply contDiff_const

theorem log_normDet_eq (A : U →L[ℝ] V) :
    Real.log A.toLinearMap.normDet = (1 / 2 : ℝ) * Real.log (gramDet A) := by
  rw [gramDet_eq, Real.log_pow]
  ring

theorem contDiffAt_log_normDet (A : U →L[ℝ] V) (injective : Function.Injective A) :
    ContDiffAt ℝ ∞ (fun B : U →L[ℝ] V => Real.log B.toLinearMap.normDet) A := by
  have nonzero : A.toLinearMap.normDet ≠ 0 := by
    intro zero
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp zero)
      (LinearMap.ker_eq_bot.mpr injective)
  have determinant : gramDet A ≠ 0 := by rw [gramDet_eq]; exact pow_ne_zero _ nonzero
  have smooth : ContDiffAt ℝ ∞ (fun B : U →L[ℝ] V => (1 / 2 : ℝ) * Real.log (gramDet B)) A :=
    contDiffAt_const.mul (contDiff_gramDet.contDiffAt.log determinant)
  exact smooth.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun B => log_normDet_eq B))

end LeanShared.LogNormDetRegularity
