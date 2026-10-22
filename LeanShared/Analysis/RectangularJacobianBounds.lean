module
public import LeanShared.Analysis.AffineGraphJacobian
public import Mathlib.LinearAlgebra.Dimension.Constructions

public noncomputable section
open scoped RealInnerProductSpace
namespace LeanShared.RectangularJacobianBounds
variable {U E ι : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

/-- A rectangular Jacobian bound derived from actual images of an orthonormal basis. -/
theorem normDet_le (b : OrthonormalBasis ι ℝ U) (A : U →L[ℝ] E)
    {L : ℝ} (hL : 0 ≤ L) (bound : ∀ i, ‖A (b i)‖ ≤ L) :
    A.toLinearMap.normDet ≤ GraphJacobian.densityBound (ι := ι) L := by
  have entries (i j : ι) :
      |(Matrix.gram ℝ (fun k => A (b k))) i j| ≤ 1 + L ^ 2 := by
    change |inner ℝ (A (b i)) (A (b j))| ≤ _
    refine (abs_real_inner_le_norm _ _).trans ?_
    have h := mul_le_mul (bound i) (bound j) (norm_nonneg _) hL
    nlinarith
  have determinant := Matrix.det_le (abv := AbsoluteValue.abs) entries
  simp only [AbsoluteValue.abs_apply, nsmul_eq_mul] at determinant
  have square : (Matrix.gram ℝ (fun i => A (b i))).det =
      A.toLinearMap.normDet ^ 2 :=
    (LinearMap.normDet_sq_eq_det_gram A.toLinearMap b).symm
  rw [← Real.sqrt_sq (LinearMap.normDet_nonneg A.toLinearMap)]
  apply Real.sqrt_le_sqrt
  apply (le_abs_self _).trans
  simpa only [square, nsmul_eq_mul] using determinant

omit [Fintype ι] [DecidableEq ι] in
/-- Projection costs only a fixed dimensional constant, independent of the map
whose tangent Jacobian is being measured. -/
theorem projected_determinant_le [FiniteDimensional ℝ E]
    (A : U →L[ℝ] E) (Q : E →L[ℝ] U) (injective : Function.Injective A) :
    |(Q.comp A).det| ≤
      GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) ‖Q‖ *
        A.toLinearMap.normDet := by
  have dim : Module.finrank ℝ A.toLinearMap.range = Module.finrank ℝ U :=
    LinearMap.finrank_range_of_inj injective
  let b := (stdOrthonormalBasis ℝ A.toLinearMap.range).reindex (finCongr dim)
  let R : A.toLinearMap.range →L[ℝ] U := Q.comp A.toLinearMap.range.subtypeL
  have bound : R.toLinearMap.normDet ≤
      GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ U)) ‖Q‖ := by
    apply normDet_le b R (norm_nonneg Q)
    intro i
    calc
      ‖R (b i)‖ ≤ ‖Q‖ * ‖(b i : E)‖ := Q.le_opNorm _
      _ = ‖Q‖ := by
        change ‖Q‖ * ‖b i‖ = ‖Q‖
        rw [b.norm_eq_one, mul_one]
  have chain := LinearMap.normDet_comp A.toLinearMap Q.toLinearMap
  change (Q.comp A).toLinearMap.normDet = R.toLinearMap.normDet * A.toLinearMap.normDet at chain
  rw [← LinearMap.normDet_eq_abs_det, chain]
  exact mul_le_mul_of_nonneg_right bound (LinearMap.normDet_nonneg _)
omit [Fintype ι] [DecidableEq ι] in
/-- The graph-to-tangent comparison has a fixed structural constant. In
particular, it contains no norm of `A` and no iterate-dependent factor. -/
theorem graph_projected_determinant_le [FiniteDimensional ℝ E]
    (V : Submodule ℝ E) (D : V →L[ℝ] Vᗮ) (A : E ≃L[ℝ] E)
    (Q : E →L[ℝ] V) {L : ℝ} (bound : ‖D‖ ≤ L) :
    |(Q.comp (A.toContinuousLinearMap.comp
        (IntrinsicGraphJacobian.graphDifferential V D))).det| ≤
      (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ V)) ‖Q‖ *
        GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ V)) L) *
      (A.toLinearMap.domRestrict
        (IntrinsicGraphJacobian.graphDifferential V D).toLinearMap.range).normDet := by
  let G := IntrinsicGraphJacobian.graphDifferential V D
  have injective : Function.Injective (A.toContinuousLinearMap.comp G) :=
    A.injective.comp (IntrinsicGraphJacobian.graphDifferential_injective V D)
  have projected := projected_determinant_le (A.toContinuousLinearMap.comp G) Q injective
  have sourceBound : G.toLinearMap.normDet ≤
      GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ V)) L := by
    rw [IntrinsicGraphJacobian.normDet_graph V (stdOrthonormalBasis ℝ V) D]
    exact GraphJacobian.density_le _ _ bound
  have chain := LinearMap.normDet_comp G.toLinearMap A.toLinearMap
  change (A.toContinuousLinearMap.comp G).toLinearMap.normDet =
    (A.toLinearMap.domRestrict G.toLinearMap.range).normDet * G.toLinearMap.normDet at chain
  rw [chain] at projected
  refine projected.trans ?_
  calc
    _ ≤ GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ V)) ‖Q‖ *
        ((A.toLinearMap.domRestrict G.toLinearMap.range).normDet *
          GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ V)) L) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left sourceBound (LinearMap.normDet_nonneg _))
        (GraphJacobian.densityBound_nonneg _)
    _ = _ := by ring
omit [Fintype ι] [DecidableEq ι] in
/-- The stable part of a graph does not change the unstable block of a map
preserving the stable subspace. -/
theorem graph_projection_comp [FiniteDimensional ℝ E]
    (V : Submodule ℝ E) (D : V →L[ℝ] Vᗮ) (A : E →L[ℝ] E)
    (stable : ∀ v ∈ Vᗮ, A v ∈ Vᗮ) :
    V.orthogonalProjectionOnto.comp (A.comp
      (IntrinsicGraphJacobian.graphDifferential V D)) =
      V.orthogonalProjectionOnto.comp (A.comp V.subtypeL) := by
  apply ContinuousLinearMap.ext
  intro v
  change V.orthogonalProjectionOnto (A ((v : E) + (D v : E))) =
    V.orthogonalProjectionOnto (A (v : E))
  rw [map_add, map_add]
  have zero : V.orthogonalProjectionOnto (A (D v : E)) = 0 :=
    (V.orthogonalProjectionOnto_eq_zero_iff).mpr (stable _ (D v).property)
  rw [zero, add_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- A genuine invariant stable splitting yields the word-independent
principal determinant comparison for every graph of the stipulated slope. -/
theorem invariant_graph_tangent_bound [FiniteDimensional ℝ E]
    (V : Submodule ℝ E) (D : V →L[ℝ] Vᗮ) (A : E ≃L[ℝ] E)
    (stable : ∀ v ∈ Vᗮ, A v ∈ Vᗮ) {L : ℝ} (bound : ‖D‖ ≤ L) :
    |(V.orthogonalProjectionOnto.comp (A.toContinuousLinearMap.comp V.subtypeL)).det| ≤
      (GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ V))
          ‖V.orthogonalProjectionOnto‖ *
        GraphJacobian.densityBound (ι := Fin (Module.finrank ℝ V)) L) *
      (A.toLinearMap.domRestrict
        (IntrinsicGraphJacobian.graphDifferential V D).toLinearMap.range).normDet := by
  have h := graph_projected_determinant_le V D A V.orthogonalProjectionOnto bound
  rw [graph_projection_comp V D A.toContinuousLinearMap stable] at h
  exact h
end LeanShared.RectangularJacobianBounds
