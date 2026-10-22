module
public import LeanShared.Analysis.ProductConeBlockFactorization
public import LeanShared.Geometry.OrthogonalProductOperatorBounds

/-! Exact adjoint coordinates and radial estimates from the actual graph
factorization. The constants four and one quarter occur only once,
independently of the length of the matrix word. -/
public noncomputable section
open Set
namespace LeanShared.TriangularAdjointRadialBounds
open OrthogonalProductCoordinates
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

theorem adjoint_formula (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (A : (X×Y) →L[ℝ] (X×Y)) (J : X →L[ℝ] X) (K : Y →L[ℝ] X)
    (L : X →L[ℝ] Y) (S : Y →L[ℝ] Y)
    (factorization : ∀ u s, A (u,s) = (J (u-K s), L (J (u-K s))+S s)) (z : X×Y) :
    (transport dimension A).adjoint (equiv dimension z) =
      equiv dimension (J.adjoint (z.1+L.adjoint z.2),
        S.adjoint z.2-K.adjoint (J.adjoint (z.1+L.adjoint z.2))) := by
  apply ext_inner_left ℝ
  intro w
  obtain ⟨⟨u,s⟩, rfl⟩ := (equiv dimension).surjective w
  rw [ContinuousLinearMap.adjoint_inner_right]
  have applyTransport : transport dimension A (equiv dimension (u,s)) = equiv dimension (A (u,s)) := by
    simp only [transport, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  rw [applyTransport, factorization, inner_map, inner_map]
  simp only [map_sub, inner_add_left, inner_sub_left, inner_add_right, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_right]
  ring

theorem first_cone_iff (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (z : X×Y) (κ : ℝ) :
    equiv dimension z ∈ ProjectionConeTransversality.cone (firstProjection dimension) κ ↔
      ‖z.1‖ ≤ κ*‖z.2‖ := by
  change ‖firstProjection dimension (equiv dimension z)‖ ≤
    κ*‖equiv dimension z-firstProjection dimension (equiv dimension z)‖ ↔ _
  rw [firstProjection_apply, ← map_sub]
  have difference : z-(z.1,0) = (0,z.2) := by ext <;> simp
  rw [difference, norm_first_axis, norm_second_axis]

theorem second_cone_iff (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (z : X×Y) (κ : ℝ) :
    equiv dimension z ∈ ProjectionConeTransversality.cone (secondProjection dimension) κ ↔
      ‖z.2‖ ≤ κ*‖z.1‖ := by
  change ‖secondProjection dimension (equiv dimension z)‖ ≤
    κ*‖equiv dimension z-secondProjection dimension (equiv dimension z)‖ ↔ _
  rw [secondProjection_apply, ← map_sub]
  have difference : z-(0,z.2) = (z.1,0) := by ext <;> simp
  rw [difference, norm_second_axis, norm_first_axis]

theorem first_strict_mem_interior (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (z : X×Y) {κ : ℝ} (strict : ‖z.1‖ < κ*‖z.2‖) :
    equiv dimension z ∈ interior (ProjectionConeTransversality.cone (firstProjection dimension) κ) := by
  let P := firstProjection dimension
  have openStrict : IsOpen {v : E | ‖P v‖ < κ*‖v-P v‖} :=
    isOpen_lt (continuous_norm.comp P.continuous)
      ((continuous_norm.comp (continuous_id.sub P.continuous)).const_mul κ)
  have inside : {v : E | ‖P v‖ < κ*‖v-P v‖} ⊆ ProjectionConeTransversality.cone P κ := by
    intro v hv
    change ‖P v‖ ≤ κ*‖v-P v‖
    exact hv.le
  have member : equiv dimension z ∈ {v : E | ‖P v‖ < κ*‖v-P v‖} := by
    change ‖firstProjection dimension (equiv dimension z)‖ <
      κ*‖equiv dimension z-firstProjection dimension (equiv dimension z)‖
    rw [firstProjection_apply, ← map_sub]
    have difference : z-(z.1,0) = (0,z.2) := by ext <;> simp
    rw [difference, norm_first_axis, norm_second_axis]
    exact strict
  exact interior_mono inside (openStrict.interior_eq.symm ▸ member)

/-- Outside the closed narrow target cone, the stable Schur block controls
the actual adjoint norm. Its loss is four, rather than four to a word length. -/
theorem upper (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (A : (X×Y) →L[ℝ] (X×Y)) (J : X →L[ℝ] X) (K : Y →L[ℝ] X)
    (L : X →L[ℝ] Y) (S : Y →L[ℝ] Y)
    (factorization : ∀ u s, A (u,s) = (J (u-K s), L (J (u-K s))+S s))
    {μ β : ℝ} (nonnegativeμ : 0 ≤ μ) (narrow : 1/2 ≤ β)
    (smallK : ‖K‖ ≤ 1/8) (stable : ‖S‖ ≤ μ) (ξ : E)
    (outside : (transport dimension A).adjoint ξ ∉
      ProjectionConeTransversality.cone (secondProjection dimension) β) :
    ‖(transport dimension A).adjoint ξ‖ ≤ 4*μ*‖ξ‖ := by
  obtain ⟨z, rfl⟩ := (equiv dimension).surjective ξ
  rw [adjoint_formula dimension A J K L S factorization z] at outside ⊢
  let u : X := J.adjoint (z.1+L.adjoint z.2)
  let s : Y := S.adjoint z.2-K.adjoint u
  have notCone : ¬ ‖s‖ ≤ β*‖u‖ := by
    simpa only [second_cone_iff] using outside
  have half : (1/2:ℝ)*‖u‖ ≤ ‖s‖ :=
    (mul_le_mul_of_nonneg_right narrow (norm_nonneg _)).trans (lt_of_not_ge notCone).le
  have boundS : ‖S.adjoint z.2‖ ≤ μ*‖z.2‖ := by
    have estimate := S.adjoint.le_opNorm z.2
    rw [ContinuousLinearMap.adjoint.norm_map] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right stable (norm_nonneg _))
  have boundK : ‖K.adjoint u‖ ≤ (1/8:ℝ)*‖u‖ := by
    have estimate := K.adjoint.le_opNorm u
    rw [ContinuousLinearMap.adjoint.norm_map] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right smallK (norm_nonneg _))
  have stableComponent : ‖s‖ ≤ μ*‖z.2‖+(1/8:ℝ)*‖u‖ :=
    (norm_sub_le _ _).trans (add_le_add boundS boundK)
  have sumBound := norm_le_axis_sum dimension (u,s)
  have total : ‖equiv dimension (u,s)‖ ≤ 4*μ*‖z.2‖ := by nlinarith
  exact total.trans (mul_le_mul_of_nonneg_left (axis_norm_le dimension z).2 (by positivity))

/-- The unstable diagonal inverse bound gives the actual radial lower
bound outside the fixed half-slope source cone, with one endpoint loss. -/
theorem lower (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (A : (X×Y) →L[ℝ] (X×Y)) (J : X ≃L[ℝ] X) (K : Y →L[ℝ] X)
    (L : X →L[ℝ] Y) (S : Y →L[ℝ] Y)
    (factorization : ∀ u s, A (u,s) = (J (u-K s), L (J (u-K s))+S s))
    {I : ℝ} (positiveI : 0 < I) (smallL : ‖L‖ ≤ 1/8)
    (inverse : ‖J.symm.toContinuousLinearMap‖ ≤ I) (ξ : E)
    (outside : ξ ∉ interior (ProjectionConeTransversality.cone (firstProjection dimension) (1/2))) :
    (4*I)⁻¹*‖ξ‖ ≤ ‖(transport dimension A).adjoint ξ‖ := by
  obtain ⟨z, rfl⟩ := (equiv dimension).surjective ξ
  rw [adjoint_formula dimension A J.toContinuousLinearMap K L S factorization z]
  let a : X := z.1+L.adjoint z.2
  let u : X := J.toContinuousLinearMap.adjoint a
  let s : Y := S.adjoint z.2-K.adjoint u
  have ratio : (1/2:ℝ)*‖z.2‖ ≤ ‖z.1‖ := not_lt.mp
    (fun strict => outside (first_strict_mem_interior dimension z strict))
  have sourceNorm : ‖equiv dimension z‖ ≤ 3*‖z.1‖ := by
    have bound := ProjectionConeTransversality.outside_bound (firstProjection dimension) (1/2)
      (by norm_num) (equiv dimension z) outside
    rw [firstProjection_apply, norm_first_axis] at bound
    norm_num at bound
    exact bound
  have boundL : ‖L.adjoint z.2‖ ≤ (1/8:ℝ)*‖z.2‖ := by
    have estimate := L.adjoint.le_opNorm z.2
    rw [ContinuousLinearMap.adjoint.norm_map] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right smallL (norm_nonneg _))
  have triangle : ‖z.1‖ ≤ ‖a‖+‖L.adjoint z.2‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (z.1+L.adjoint z.2) (L.adjoint z.2)
  have undo : J.symm.toContinuousLinearMap.adjoint (J.toContinuousLinearMap.adjoint a) = a := by
    have identity : J.symm.toContinuousLinearMap.adjoint.comp J.toContinuousLinearMap.adjoint =
        ContinuousLinearMap.id ℝ X := by
      rw [← ContinuousLinearMap.adjoint_comp]
      rw [show J.toContinuousLinearMap.comp J.symm.toContinuousLinearMap = ContinuousLinearMap.id ℝ X from by
        ext v
        exact J.apply_symm_apply v]
      exact ContinuousLinearMap.adjoint_id
    exact congrArg (fun B : X →L[ℝ] X => B a) identity
  have boundJ : ‖a‖ ≤ I*‖u‖ := by
    have estimate := J.symm.toContinuousLinearMap.adjoint.le_opNorm (J.toContinuousLinearMap.adjoint a)
    rw [undo, ContinuousLinearMap.adjoint.norm_map] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right inverse (norm_nonneg _))
  have initial : ‖equiv dimension z‖ ≤ 4*I*‖u‖ := by nlinarith
  have total : ‖equiv dimension z‖ ≤ (4*I)*‖equiv dimension (u,s)‖ := initial.trans
    (mul_le_mul_of_nonneg_left (axis_norm_le dimension (u,s)).1 (by positivity))
  have divide : ‖equiv dimension z‖/(4*I) ≤ ‖equiv dimension (u,s)‖ :=
    (div_le_iff₀ (by positivity : 0 < 4*I)).mpr (by nlinarith)
  simpa only [div_eq_mul_inv, mul_comm] using divide

/-- The phase-gap consumer may use membership of the closed narrow cone
as the alternative to stable radial contraction. -/
theorem closed_narrow_or_upper (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (A : (X×Y) →L[ℝ] (X×Y)) (J : X →L[ℝ] X) (K : Y →L[ℝ] X)
    (L : X →L[ℝ] Y) (S : Y →L[ℝ] Y)
    (factorization : ∀ u s, A (u,s) = (J (u-K s), L (J (u-K s))+S s))
    {μ β : ℝ} (nonnegativeμ : 0 ≤ μ) (narrow : 1/2 ≤ β)
    (smallK : ‖K‖ ≤ 1/8) (stable : ‖S‖ ≤ μ) (ξ : E) :
    (transport dimension A).adjoint ξ ∈ ProjectionConeTransversality.cone (secondProjection dimension) β ∨
      ‖(transport dimension A).adjoint ξ‖ ≤ 4*μ*‖ξ‖ := by
  by_cases member : (transport dimension A).adjoint ξ ∈
      ProjectionConeTransversality.cone (secondProjection dimension) β
  · exact Or.inl member
  · exact Or.inr (upper dimension A J K L S factorization nonnegativeμ narrow smallK stable ξ member)

end LeanShared.TriangularAdjointRadialBounds
