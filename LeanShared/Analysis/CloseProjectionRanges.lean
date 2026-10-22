module
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Linarith

/-! Norm-close actual idempotent projections give explicit equivalences of
their ranges. The inverse bound is quantitative. This supplies the local
splitting-frame step of hyperbolic chart constructions without assuming a
global trivialization of the stable or unstable bundle. -/
public noncomputable section
namespace LeanShared.CloseProjectionRanges

@[expose] def rangeMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : E →L[ℝ] E) : P.range →L[ℝ] Q.range :=
  (Q.comp P.range.subtypeL).codRestrict Q.range (fun x => ⟨x.val, rfl⟩)

theorem rangeMap_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : E →L[ℝ] E) (x : P.range) : (rangeMap P Q x).val = Q x.val := rfl

theorem lower_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : E →L[ℝ] E) (idempotent : ∀ x, P (P x) = P x) (x : P.range) :
    (1 - ‖P - Q‖) * ‖x‖ ≤ ‖rangeMap P Q x‖ := by
  have fixed : P x.val = x.val := by
    obtain ⟨y, image⟩ := x.property
    change P y = x.val at image
    rw [← image]
    exact idempotent y
  have identity : x.val = (P - Q) x.val + Q x.val := by
    rw [sub_apply, sub_add_cancel, fixed]
  have estimate : ‖x.val‖ ≤ ‖P - Q‖ * ‖x.val‖ + ‖Q x.val‖ :=
    calc
      _ = ‖(P - Q) x.val + Q x.val‖ := congrArg norm identity
      _ ≤ ‖(P - Q) x.val‖ + ‖Q x.val‖ := norm_add_le _ _
      _ ≤ _ := add_le_add ((P - Q).le_opNorm x.val) le_rfl
  change (1 - ‖P - Q‖) * ‖x.val‖ ≤ ‖Q x.val‖
  nlinarith

theorem rangeMap_injective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : E →L[ℝ] E) (idempotent : ∀ x, P (P x) = P x)
    (close : ‖P - Q‖ < 1) : Function.Injective (rangeMap P Q) := by
  intro x y equality
  have zero : rangeMap P Q (x - y) = 0 := by rw [map_sub, equality, sub_self]
  have estimate := lower_bound P Q idempotent (x - y)
  rw [zero, norm_zero] at estimate
  have vanishes : ‖x - y‖ = 0 := by
    have nonnegative := norm_nonneg (x - y)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp vanishes)

theorem finrank_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (P Q : E →L[ℝ] E)
    (idempotentP : ∀ x, P (P x) = P x) (idempotentQ : ∀ x, Q (Q x) = Q x)
    (close : ‖P - Q‖ < 1) : Module.finrank ℝ P.range = Module.finrank ℝ Q.range := by
  apply le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective
      (f := (rangeMap P Q).toLinearMap) (rangeMap_injective P Q idempotentP close)
  · exact LinearMap.finrank_le_finrank_of_injective
      (f := (rangeMap Q P).toLinearMap) (rangeMap_injective Q P idempotentQ
        (by simpa only [norm_sub_rev] using close))

@[expose] def rangeEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (P Q : E →L[ℝ] E)
    (idempotentP : ∀ x, P (P x) = P x) (idempotentQ : ∀ x, Q (Q x) = Q x)
    (close : ‖P - Q‖ < 1) : P.range ≃L[ℝ] Q.range :=
  ContinuousLinearEquiv.ofBijective (rangeMap P Q)
    (LinearMap.ker_eq_bot.mpr (rangeMap_injective P Q idempotentP close))
    (LinearMap.range_eq_top.mpr
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (finrank_eq P Q idempotentP idempotentQ close)).mp
          (rangeMap_injective P Q idempotentP close)))

theorem inverse_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (P Q : E →L[ℝ] E)
    (idempotentP : ∀ x, P (P x) = P x) (idempotentQ : ∀ x, Q (Q x) = Q x)
    (close : ‖P - Q‖ < 1) (y : Q.range) :
    ‖(rangeEquiv P Q idempotentP idempotentQ close).symm y‖ ≤ ‖y‖ / (1 - ‖P - Q‖) := by
  apply (le_div_iff₀ (sub_pos.mpr close)).mpr
  rw [mul_comm]
  have estimate := lower_bound P Q idempotentP
    ((rangeEquiv P Q idempotentP idempotentQ close).symm y)
  have inverse := (rangeEquiv P Q idempotentP idempotentQ close).apply_symm_apply y
  change rangeMap P Q ((rangeEquiv P Q idempotentP idempotentQ close).symm y) = y at inverse
  rw [inverse] at estimate
  exact estimate

end LeanShared.CloseProjectionRanges
