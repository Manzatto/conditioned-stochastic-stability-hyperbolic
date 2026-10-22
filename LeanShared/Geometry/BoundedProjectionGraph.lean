module
public import LeanShared.Geometry.ProjectionComplementGraph

/-! Actual graph coordinates and quantitative slope from a transverse
subspace's orthogonal projection bound. -/
public noncomputable section
namespace LeanShared.BoundedProjectionGraph
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_graph (U W : Submodule ℝ E)
    (dimension : Module.finrank ℝ W = Module.finrank ℝ U)
    {L : ℝ} (nonnegative : 0 ≤ L)
    (slope : ∀ w : W, ‖Uᗮ.orthogonalProjectionOnto (w : E)‖ ≤
      L * ‖U.orthogonalProjectionOnto (w : E)‖) :
    ∃ D : U →L[ℝ] Uᗮ, ‖D‖ ≤ L ∧
      (IntrinsicGraphJacobian.graphDifferential U D).toLinearMap.range = W := by
  let P := U.orthogonalProjectionOnto.comp W.subtypeL
  have injective : Function.Injective P := by
    intro a b equal
    have zero : P (a - b) = 0 := by rw [map_sub, equal, sub_self]
    have orthZero : Uᗮ.orthogonalProjectionOnto ((a-b : W) : E) = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      simpa only [show U.orthogonalProjectionOnto ((a-b : W) : E) = 0 from zero,
        norm_zero, mul_zero] using slope (a-b)
    have decomposition := U.starProjection_add_starProjection_orthogonal ((a-b : W) : E)
    have valueZero : ((a-b : W) : E) = 0 := by
      change (U.orthogonalProjectionOnto ((a-b : W) : E) : E) +
        (Uᗮ.orthogonalProjectionOnto ((a-b : W) : E) : E) = _ at decomposition
      rw [show U.orthogonalProjectionOnto ((a-b : W) : E) = 0 from zero,
        orthZero] at decomposition
      exact decomposition.symm.trans (by simp)
    exact sub_eq_zero.mp (Subtype.ext valueZero)
  let e : W ≃L[ℝ] U :=
    (P.toLinearMap.linearEquivOfInjective injective dimension).toContinuousLinearEquiv
  let D := Uᗮ.orthogonalProjectionOnto.comp (W.subtypeL.comp e.symm.toContinuousLinearMap)
  have projection (u : U) : U.orthogonalProjectionOnto (e.symm u : E) = u :=
    e.apply_symm_apply u
  have graph (u : U) : IntrinsicGraphJacobian.graphDifferential U D u = (e.symm u : E) := by
    change (u : E) + (Uᗮ.orthogonalProjectionOnto (e.symm u : E) : E) = _
    have same : U.starProjection (e.symm u : E) = (u : E) := congrArg Subtype.val (projection u)
    rw [← same]
    exact U.starProjection_add_starProjection_orthogonal _
  refine ⟨D, ContinuousLinearMap.opNorm_le_bound _ nonnegative ?_, ?_⟩
  · intro u
    change ‖Uᗮ.orthogonalProjectionOnto (e.symm u : E)‖ ≤ L * ‖u‖
    exact (slope (e.symm u)).trans_eq (by rw [projection])
  · ext x
    constructor
    · rintro ⟨u, rfl⟩
      rw [show (IntrinsicGraphJacobian.graphDifferential U D).toLinearMap u =
        (e.symm u : E) from graph u]
      exact (e.symm u).property
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      exact (graph (e ⟨x, hx⟩)).trans (congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩))
end LeanShared.BoundedProjectionGraph
