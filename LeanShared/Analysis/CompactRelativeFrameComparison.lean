module
public import LeanShared.Analysis.ContinuousLinearFrameInverse
public import LeanShared.Topology.CompactNearDiagonalContinuity
public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FieldSimp

/-! Nearby references in a continuous frame patch have a uniformly small
relative frame error. The second reference may lie outside the smaller
compact patch, but remains in the genuine larger frame domain. -/
public noncomputable section
open Set
namespace LeanShared.CompactRelativeFrameComparison
variable {X P E : Type*} [MetricSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_radius (U K : Set X) (openU : IsOpen U) (compact : IsCompact K)
    (inside : K ⊆ U) (f : U → P ≃L[ℝ] E)
    (continuous : Continuous (fun x => (f x).toContinuousLinearMap))
    (δ : ℝ) (positiveδ : 0 < δ) :
    ∃ η > 0, ∀ x (hx : x ∈ K), ∀ y, dist x y < η →
      ∃ hy : y ∈ U, ‖(f ⟨x, inside hx⟩).symm.toContinuousLinearMap.comp
        (f ⟨y, hy⟩).toContinuousLinearMap - ContinuousLinearMap.id ℝ P‖ < δ := by
  classical
  let F : X → P →L[ℝ] E := fun x =>
    if hx : x ∈ U then (f ⟨x, hx⟩).toContinuousLinearMap else 0
  let G : X → E →L[ℝ] P := fun x =>
    if hx : x ∈ U then (f ⟨x, hx⟩).symm.toContinuousLinearMap else 0
  have sameF (x : X) (hx : x ∈ U) : F x = (f ⟨x, hx⟩).toContinuousLinearMap := dite_eq_left hx
  have sameG (x : X) (hx : x ∈ U) : G x = (f ⟨x, hx⟩).symm.toContinuousLinearMap := dite_eq_left hx
  have cf : ContinuousOn F U := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact continuous.congr (fun x => (sameF x.val x.property).symm)
  have cg : ContinuousOn G U := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (ContinuousLinearFrameInverse.continuous_inverse f continuous).congr
      (fun x => (sameG x.val x.property).symm)
  obtain ⟨B, positiveB, bound⟩ :=
    (compact.image_of_continuousOn (cg.mono inside)).isBounded.exists_pos_norm_le
  obtain ⟨η, positiveη, close⟩ := CompactNearDiagonalContinuity.exists_radius
    K U compact openU inside F cf (δ / B) (div_pos positiveδ positiveB)
  refine ⟨η, positiveη, ?_⟩
  intro x hx y small
  obtain ⟨hy, near⟩ := close x hx y small
  refine ⟨hy, ?_⟩
  have inverseBound : ‖(f ⟨x, inside hx⟩).symm.toContinuousLinearMap‖ ≤ B := by
    rw [← sameG x (inside hx)]
    exact bound (G x) ⟨x, hx, rfl⟩
  have difference : ‖(f ⟨y, hy⟩).toContinuousLinearMap -
      (f ⟨x, inside hx⟩).toContinuousLinearMap‖ < δ / B := by
    simpa only [sameF x (inside hx), sameF y hy, dist_eq_norm, norm_sub_rev] using near
  have identity : (f ⟨x, inside hx⟩).symm.toContinuousLinearMap.comp
      (f ⟨y, hy⟩).toContinuousLinearMap - ContinuousLinearMap.id ℝ P =
      (f ⟨x, inside hx⟩).symm.toContinuousLinearMap.comp
        ((f ⟨y, hy⟩).toContinuousLinearMap - (f ⟨x, inside hx⟩).toContinuousLinearMap) := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearEquiv.coe_symm_comp_coe]
  rw [identity]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans_lt
  apply (mul_le_mul_of_nonneg_right inverseBound (norm_nonneg _)).trans_lt
  have cancellation : B * (δ / B) = δ := by field_simp
  simpa only [cancellation] using mul_lt_mul_of_pos_left difference positiveB

end LeanShared.CompactRelativeFrameComparison
