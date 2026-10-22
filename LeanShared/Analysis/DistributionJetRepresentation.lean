module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Analysis.Complex.Basic

/-!
# Distribution order bounds produce actual jet-dual representations

A distribution pairing bounded by the norm of a linear test jet annihilates
the jet kernel. Quotient descent produces its functional on the actual jet
range. The order bound makes this functional continuous and makes the entire
distribution-to-jet-dual assignment a bounded complex linear map.
Neither a representation map nor injectivity of the test jet is assumed.
-/

@[expose] public noncomputable section

namespace LeanShared.DistributionJetRepresentation

variable {Tests V B : Type*} [AddCommGroup Tests] [Module ℂ Tests]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  (J : Tests →ₗ[ℂ] V) (p : B →ₗ[ℂ] (Tests →ₗ[ℂ] ℂ))
  (C : ℝ) (hC : 0 ≤ C)
  (hbound : ∀ b t, ‖p b t‖ ≤ C * ‖b‖ * ‖J t‖)

local instance jetRangeNormedSpace : NormedSpace ℂ J.range := inferInstance

include hbound

/-- The distribution order bound forces annihilation of the jet kernel. -/
theorem ker_le (b : B) : J.ker ≤ (p b).ker := by
  intro t ht
  change p b t = 0
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  exact (hbound b t).trans_eq (by rw [show J t = 0 from ht, norm_zero, mul_zero])

/-- Algebraic descent through the actual jet kernel and first isomorphism
theorem; distinct tests with equal jets define the same value. -/
def algebraicFunctional (b : B) : J.range →ₗ[ℂ] ℂ :=
  (J.ker.liftQ (p b) (ker_le J p C hbound b)).comp J.quotKerEquivRange.symm.toLinearMap

@[simp]
theorem algebraicFunctional_core (b : B) (t : Tests) :
    algebraicFunctional J p C hbound b ⟨J t, ⟨t, rfl⟩⟩ = p b t := by
  simp only [algebraicFunctional, LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

theorem algebraicFunctional_bound (b : B) (z : J.range) :
    ‖algebraicFunctional J p C hbound b z‖ ≤ (C * ‖b‖) * ‖z‖ := by
  obtain ⟨z, t, ht⟩ := z
  subst z
  rw [algebraicFunctional_core]
  exact hbound b t

/-- The actual continuous functional on the jet range. -/
def functional (b : B) : J.range →L[ℂ] ℂ :=
  (algebraicFunctional J p C hbound b).mkContinuous (C * ‖b‖)
    (algebraicFunctional_bound J p C hbound b)

@[simp]
theorem functional_core (b : B) (t : Tests) :
    functional J p C hbound b ⟨J t, ⟨t, rfl⟩⟩ = p b t :=
  algebraicFunctional_core J p C hbound b t

include hC in
theorem functional_norm_le (b : B) : ‖functional J p C hbound b‖ ≤ C * ‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg b))
  exact algebraicFunctional_bound J p C hbound b

/-- Linearity in the distribution follows from exact jet evaluation, not
from a chosen noncanonical extension off the jet range. -/
def representationLinearMap : B →ₗ[ℂ] (J.range →L[ℂ] ℂ) where
  toFun := functional J p C hbound
  map_add' b d := by
    apply ContinuousLinearMap.ext
    rintro ⟨z, t, ht⟩
    subst z
    simp only [functional_core, add_apply]
    rw [map_add]
    rfl
  map_smul' c b := by
    apply ContinuousLinearMap.ext
    rintro ⟨z, t, ht⟩
    subst z
    simp only [functional_core, smul_apply, RingHom.id_apply]
    rw [map_smul]
    rfl

/-- The order bound itself constructs the required bounded representation. -/
def representation : B →L[ℂ] (J.range →L[ℂ] ℂ) where
  toLinearMap := representationLinearMap J p C hbound
  cont := AddMonoidHomClass.continuous_of_bound (representationLinearMap J p C hbound) C
    (fun b => functional_norm_le J p C hC hbound b)

@[simp]
theorem representation_core (b : B) (t : Tests) :
    representation J p C hC hbound b ⟨J t, ⟨t, rfl⟩⟩ = p b t :=
  functional_core J p C hbound b t

theorem representation_norm_le : ‖representation J p C hC hbound‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  exact functional_norm_le J p C hC hbound

/-- The constructed functional on the jet range is uniquely determined by
the original pairing on all tests. -/
theorem representation_unique (S : B →L[ℂ] (J.range →L[ℂ] ℂ))
    (hS : ∀ b t, S b ⟨J t, ⟨t, rfl⟩⟩ = p b t) :
    S = representation J p C hC hbound := by
  apply ContinuousLinearMap.ext
  intro b
  apply ContinuousLinearMap.ext
  rintro ⟨z, t, ht⟩
  subst z
  rw [hS, representation_core]

end LeanShared.DistributionJetRepresentation
