module

public import LeanShared.Dynamics.OneSidedPositiveEigenfunction
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.Order.Compact

/-! A proved strictly positive Ruelle eigenfunction gives the actual
continuous multiplication conjugacy to a positive unital Markov
operator.  Its uniform operator norm is exactly one.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function PositiveContinuousOperatorNorm
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop}

@[expose] def transferInverseDensity (h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (positiveEigenvalue : 0 < eigenvalue) (positiveH : ∀ a, 0 < h a) : C(FuturePath R, ℝ) :=
  ⟨fun a => (eigenvalue * h a)⁻¹, (continuous_const.mul h.continuous).inv₀
    (fun a => mul_ne_zero positiveEigenvalue.ne' (positiveH a).ne')⟩

@[expose] def normalizedTransferOperator (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (positiveEigenvalue : 0 < eigenvalue) (positiveH : ∀ a, 0 < h a) :
    C(FuturePath R, ℝ) →L[ℝ] C(FuturePath R, ℝ) :=
  (ContinuousLinearMap.mul ℝ C(FuturePath R, ℝ)
      (transferInverseDensity h eigenvalue positiveEigenvalue positiveH)).comp
    ((weightedTransferOperator ψ).comp (ContinuousLinearMap.mul ℝ C(FuturePath R, ℝ) h))

theorem normalizedTransferOperator_apply (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (positiveEigenvalue : 0 < eigenvalue) (positiveH : ∀ a, 0 < h a)
    (f : C(FuturePath R, ℝ)) (a : FuturePath R) :
    normalizedTransferOperator ψ h eigenvalue positiveEigenvalue positiveH f a =
      (eigenvalue * h a)⁻¹ * weightedTransferOperator ψ (h * f) a := rfl

theorem normalizedTransferOperator_positive (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (positiveEigenvalue : 0 < eigenvalue) (positiveH : ∀ a, 0 < h a) :
    Positive (normalizedTransferOperator ψ h eigenvalue positiveEigenvalue positiveH) := by
  intro f nonnegative a
  rw [normalizedTransferOperator_apply]
  exact mul_nonneg (inv_nonneg.mpr (mul_nonneg positiveEigenvalue.le (positiveH a).le))
    (weightedTransferOperator_positive ψ (h * f) (fun b => mul_nonneg (positiveH b).le (nonnegative b)) a)

theorem normalizedTransferOperator_one (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (positiveEigenvalue : 0 < eigenvalue) (positiveH : ∀ a, 0 < h a)
    (eigen : weightedTransferOperator ψ h = eigenvalue • h) :
    normalizedTransferOperator ψ h eigenvalue positiveEigenvalue positiveH 1 = 1 := by
  apply ContinuousMap.ext
  intro a
  rw [normalizedTransferOperator_apply, mul_one, eigen]
  change (eigenvalue * h a)⁻¹ * (eigenvalue * h a) = 1
  exact inv_mul_cancel₀ (mul_ne_zero positiveEigenvalue.ne' (positiveH a).ne')

theorem normalizedTransferOperator_conjugacy (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (positiveEigenvalue : 0 < eigenvalue) (positiveH : ∀ a, 0 < h a) (f : C(FuturePath R, ℝ)) :
    eigenvalue • (h * normalizedTransferOperator ψ h eigenvalue positiveEigenvalue positiveH f) =
      weightedTransferOperator ψ (h * f) := by
  apply ContinuousMap.ext
  intro a
  change eigenvalue * (h a * ((eigenvalue * h a)⁻¹ * weightedTransferOperator ψ (h * f) a)) = _
  field_simp [positiveEigenvalue.ne', (positiveH a).ne']

variable [Nonempty (FuturePath R)]

theorem normalizedTransferOperator_norm (ψ h : C(FuturePath R, ℝ)) (eigenvalue : ℝ)
    (positiveEigenvalue : 0 < eigenvalue) (positiveH : ∀ a, 0 < h a)
    (eigen : weightedTransferOperator ψ h = eigenvalue • h) :
    ‖normalizedTransferOperator ψ h eigenvalue positiveEigenvalue positiveH‖ = 1 := by
  rw [norm_eq_image_one _ (normalizedTransferOperator_positive ψ h eigenvalue positiveEigenvalue positiveH),
    normalizedTransferOperator_one ψ h eigenvalue positiveEigenvalue positiveH eigen, norm_one]

omit [Fintype A] in
theorem positive_eigenfunction_uniform_lower (h : C(FuturePath R, ℝ)) (positiveH : ∀ a, 0 < h a) :
    ∃ c > 0, ∀ a, c ≤ h a := by
  obtain ⟨a, _, minimal⟩ := isCompact_univ.exists_isMinOn (s := (univ : Set (FuturePath R)))
    univ_nonempty h.continuous.continuousOn
  exact ⟨h a, positiveH a, fun b => minimal (mem_univ b)⟩

end LeanShared.BilateralShadowingCoding
