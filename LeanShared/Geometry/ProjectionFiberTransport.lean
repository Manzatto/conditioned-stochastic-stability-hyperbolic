module
public import LeanShared.Geometry.BundleEndomorphismCoordinates
public import Mathlib.Tactic.Linarith

/-! Coordinate intertwining gives an actual equivalence of different bundle
fibers preserving the physical splitting. Native fiber norms are retained;
the coordinate trivialization factors appear explicitly in both bounds. -/
public noncomputable section
namespace LeanShared.ProjectionFiberTransport
open Bundle

variable {B F : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

@[expose] def map (e : Trivialization F (TotalSpace.proj (E := E))) [e.IsLinear ℝ]
    (x y : B) (hx : x ∈ e.baseSet) (hy : y ∈ e.baseSet) (R : F ≃L[ℝ] F) : E x ≃L[ℝ] E y :=
  (e.continuousLinearEquivAt ℝ x hx).trans (R.trans (e.continuousLinearEquivAt ℝ y hy).symm)

omit [VectorBundle ℝ F E] in
theorem map_apply (e : Trivialization F (TotalSpace.proj (E := E))) [e.IsLinear ℝ]
    (x y : B) (hx : x ∈ e.baseSet) (hy : y ∈ e.baseSet) (R : F ≃L[ℝ] F) (v : E x) :
    map E e x y hx hy R v = e.symmL ℝ y (R (e.continuousLinearMapAt ℝ x v)) := by
  simp only [map, ContinuousLinearEquiv.trans_apply,
    Trivialization.coe_continuousLinearEquivAt_eq,
    Trivialization.symm_continuousLinearEquivAt_eq]

theorem intertwines (e : Trivialization F (TotalSpace.proj (E := E))) [e.IsLinear ℝ]
    (P : ∀ b, E b →L[ℝ] E b) (x y : B) (hx : x ∈ e.baseSet) (hy : y ∈ e.baseSet)
    (R : F ≃L[ℝ] F)
    (commutes : (BundleEndomorphismCoordinates.coordinates E e P y).comp R.toContinuousLinearMap =
      R.toContinuousLinearMap.comp (BundleEndomorphismCoordinates.coordinates E e P x)) (v : E x) :
    P y (map E e x y hx hy R v) = map E e x y hx hy R (P x v) := by
  apply (e.continuousLinearEquivAt ℝ y hy).injective
  have coordinate := congrArg (fun A : F →L[ℝ] F => A (e.continuousLinearMapAt ℝ x v)) commutes
  simp only [BundleEndomorphismCoordinates.coordinates, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_apply, e.symmL_continuousLinearMapAt hx] at coordinate
  simpa only [map_apply, Trivialization.coe_continuousLinearEquivAt_eq,
    e.continuousLinearMapAt_symmL hy] using coordinate

omit [VectorBundle ℝ F E] in
theorem norm_le (e : Trivialization F (TotalSpace.proj (E := E))) [e.IsLinear ℝ]
    (x y : B) (hx : x ∈ e.baseSet) (hy : y ∈ e.baseSet) (R : F ≃L[ℝ] F)
    (C D : ℝ) (forward : ‖e.continuousLinearMapAt ℝ x‖ ≤ C)
    (inverse : ‖e.symmL ℝ y‖ ≤ D) :
    ‖(map E e x y hx hy R).toContinuousLinearMap‖ ≤ D * ‖R.toContinuousLinearMap‖ * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    have nonnegC := (norm_nonneg _).trans forward
    have nonnegD := (norm_nonneg _).trans inverse
    positivity)
  intro v
  change ‖map E e x y hx hy R v‖ ≤ _
  rw [map_apply]
  calc
    _ ≤ ‖e.symmL ℝ y‖ * ‖R (e.continuousLinearMapAt ℝ x v)‖ := (e.symmL ℝ y).le_opNorm _
    _ ≤ D * (‖R.toContinuousLinearMap‖ * (C * ‖v‖)) := by
      apply mul_le_mul inverse
      · exact (R.toContinuousLinearMap.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left
            (((e.continuousLinearMapAt ℝ x).le_opNorm v).trans
              (mul_le_mul_of_nonneg_right forward (norm_nonneg _))) (norm_nonneg _))
      · exact norm_nonneg _
      · exact (norm_nonneg _).trans inverse
    _ = _ := by ring

omit [VectorBundle ℝ F E] in
theorem inverse_norm_le (e : Trivialization F (TotalSpace.proj (E := E))) [e.IsLinear ℝ]
    (x y : B) (hx : x ∈ e.baseSet) (hy : y ∈ e.baseSet) (R : F ≃L[ℝ] F)
    (C D : ℝ) (forward : ‖e.continuousLinearMapAt ℝ y‖ ≤ C)
    (inverse : ‖e.symmL ℝ x‖ ≤ D) :
    ‖(map E e x y hx hy R).symm.toContinuousLinearMap‖ ≤ D * ‖R.symm.toContinuousLinearMap‖ * C := by
  have identity : (map E e x y hx hy R).symm = map E e y x hy hx R.symm := by
    apply ContinuousLinearEquiv.toLinearEquiv_injective
    rfl
  rw [identity]
  exact norm_le E e y x hy hx R.symm C D forward inverse

end LeanShared.ProjectionFiberTransport
