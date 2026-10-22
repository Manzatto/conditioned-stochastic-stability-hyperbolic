module
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Full-rank linear control maps admit actual continuous kernel/target
coordinates. No complement, inverse chart, or completed-space comparison
is a source input. Arbitrary finite-dimensional control norms are allowed. -/
public noncomputable section
namespace LeanShared.SubmersionLinearCoordinates
open Function

theorem exists_kernel_coordinates
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (D : E →L[ℝ] F) (surjective : Function.Surjective D) :
    ∃ P : E →L[ℝ] D.ker, ∃ e : E ≃L[ℝ] (D.ker × F), ∀ x, e x = (P x, D x) := by
  obtain ⟨r, hr⟩ := D.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr surjective)
  have right (y : F) : D (r y) = y := congrArg (fun L : F →ₗ[ℝ] F => L y) hr
  let rC : F →L[ℝ] E := r.toContinuousLinearMap
  let P : E →L[ℝ] D.ker :=
    ((ContinuousLinearMap.id ℝ E) - rC.comp D).codRestrict D.ker (by
      intro x
      change D (x - r (D x)) = 0
      rw [map_sub, right, sub_self])
  let A : E →L[ℝ] (D.ker × F) := P.prod D
  have injective : Function.Injective A := by
    intro x y h
    have hp : P x = P y := congrArg Prod.fst h
    have hd : D x = D y := congrArg Prod.snd h
    have equality := congrArg Subtype.val hp
    change x - r (D x) = y - r (D y) at equality
    rw [hd] at equality
    exact sub_left_inj.mp equality
  have onto : Function.Surjective A := by
    rintro ⟨a, b⟩
    refine ⟨a.val + r b, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change (a.val + r b) - r (D (a.val + r b)) = a.val
      rw [map_add, show D a.val = 0 from a.property, right, zero_add, add_sub_cancel_right]
    · change D (a.val + r b) = b
      rw [map_add, show D a.val = 0 from a.property, right, zero_add]
  let e := ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr injective)
    (LinearMap.range_eq_top.mpr onto)
  exact ⟨P, e, fun _ => rfl⟩
end LeanShared.SubmersionLinearCoordinates
