module
public import LeanShared.Analysis.ProjectionConeSourceRateMargin
public import LeanShared.Analysis.ProjectionConeRadialMargin
public import LeanShared.Analysis.OrthogonalDiagonalRateConeBounds
public import LeanShared.Geometry.OrthogonalProductCoordinateCalculus

/-! One-step cone hyperbolicity for the adjoint of a derivative close to the
hyperbolic diagonal block. The plus frequency cone keeps opening one half; the
minus cone and the narrow target cone are adapted to the one-step rate `q`, so
that a single step already sends the complement of the plus cone into the
narrow cone (manuscript, Definition `def:cone-adapted`). -/
public noncomputable section
namespace LeanShared.OneStepConePolarization
open Set OrthogonalProductCoordinates
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

@[expose] def narrowOpening (q : ℝ) : ℝ := 1 + q ^ 2
@[expose] def minusOpening (q : ℝ) : ℝ := (3 + q ^ 2) / 2

theorem opening_bounds {q : ℝ} (positive : 0 < q) (contracting : q < 1) :
    (1/4 : ℝ) ≤ narrowOpening q ∧ 0 ≤ narrowOpening q ∧ narrowOpening q < 2 ∧
    narrowOpening q < minusOpening q ∧ minusOpening q < 2 ∧ 0 ≤ minusOpening q ∧
    0 < ProjectionConeRateMargin.tolerance q ∧
    q ^ 2 * 2 + q * (1 + 2) * ProjectionConeRateMargin.tolerance q * (1 + narrowOpening q) <
      narrowOpening q := by
  unfold narrowOpening minusOpening ProjectionConeRateMargin.tolerance
  have square : q ^ 2 < 1 := by nlinarith
  have h1 : 0 < 1 - q ^ 2 := by linarith
  have h2 : 3 * q * (2 + q ^ 2) < 9 := by nlinarith
  refine ⟨by nlinarith, by positivity, by linarith, by linarith, by linarith, by positivity,
    by linarith, ?_⟩
  nlinarith [mul_pos h1 (show (0:ℝ) < 16 - 3 * q * (2 + q ^ 2) by linarith)]

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E] in
theorem cone_mono {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (P : Z →L[ℝ] Z) {κ κ' : ℝ} (le : κ ≤ κ') {v : Z}
    (member : v ∈ ProjectionConeTransversality.cone P κ) :
    v ∈ ProjectionConeTransversality.cone P κ' := by
  change ‖P v‖ ≤ κ' * ‖v - P v‖
  exact member.trans (mul_le_mul_of_nonneg_right le (norm_nonneg _))

theorem first_complement (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E) (v : E) :
    v - firstProjection dimension v = secondProjection dimension v :=
  sub_eq_iff_eq_add.mpr (projections_add dimension v).symm

theorem second_complement (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E) (v : E) :
    v - secondProjection dimension v = firstProjection dimension v :=
  sub_eq_iff_eq_add.mpr ((add_comm _ _).trans (projections_add dimension v)).symm

theorem outside_half_mem_second (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (v : E) (outside : v ∉ interior
      (ProjectionConeTransversality.cone (firstProjection dimension) (1/2))) :
    v ∈ ProjectionConeTransversality.cone (secondProjection dimension) 2 := by
  have notStrict : ¬ ‖firstProjection dimension v‖ <
      (1/2) * ‖v - firstProjection dimension v‖ := by
    intro strict
    apply outside
    have openStrict : IsOpen {w : E | ‖firstProjection dimension w‖ <
        (1/2) * ‖w - firstProjection dimension w‖} :=
      isOpen_lt (continuous_norm.comp (firstProjection dimension).continuous)
        ((continuous_norm.comp (continuous_id.sub (firstProjection dimension).continuous)).const_mul _)
    have subset : {w : E | ‖firstProjection dimension w‖ <
        (1/2) * ‖w - firstProjection dimension w‖} ⊆
        ProjectionConeTransversality.cone (firstProjection dimension) (1/2) := by
      intro w hw
      change ‖firstProjection dimension w‖ < (1/2) * ‖w - firstProjection dimension w‖ at hw
      change ‖firstProjection dimension w‖ ≤ (1/2) * ‖w - firstProjection dimension w‖
      exact hw.le
    apply interior_mono subset
    rw [openStrict.interior_eq]
    exact strict
  rw [first_complement] at notStrict
  change ‖secondProjection dimension v‖ ≤ 2 * ‖v - secondProjection dimension v‖
  rw [second_complement]
  linarith [not_lt.mp notStrict]

theorem cones_meet_zero (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    {γ : ℝ} (_nonneg : 0 ≤ γ) (small : γ < 2) {w : E}
    (plus : w ∈ ProjectionConeTransversality.cone (firstProjection dimension) (1/2))
    (minus : w ∈ ProjectionConeTransversality.cone (secondProjection dimension) γ) : w = 0 := by
  change ‖firstProjection dimension w‖ ≤ (1/2) * ‖w - firstProjection dimension w‖ at plus
  change ‖secondProjection dimension w‖ ≤ γ * ‖w - secondProjection dimension w‖ at minus
  rw [first_complement] at plus
  rw [second_complement] at minus
  have zeroFirst : ‖firstProjection dimension w‖ = 0 := by
    nlinarith [norm_nonneg (firstProjection dimension w), norm_nonneg (secondProjection dimension w)]
  have zeroSecond : ‖secondProjection dimension w‖ = 0 := by
    rw [zeroFirst, mul_zero] at minus
    exact le_antisymm minus (norm_nonneg _)
  rw [← projections_add dimension w, norm_eq_zero.mp zeroFirst, norm_eq_zero.mp zeroSecond, add_zero]

theorem not_mem_interior_half (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    {γ : ℝ} (nonneg : 0 ≤ γ) (small : γ < 2) {w : E}
    (member : w ∈ ProjectionConeTransversality.cone (secondProjection dimension) γ)
    (nonzero : w ≠ 0) :
    w ∉ interior (ProjectionConeTransversality.cone (firstProjection dimension) (1/2)) :=
  fun inside => nonzero (cones_meet_zero dimension nonneg small (interior_subset inside) member)

theorem half_minus_disjoint (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    {γ : ℝ} (nonneg : 0 ≤ γ) (small : γ < 2) :
    ∀ ξ ∈ ProjectionConeTransversality.cone (firstProjection dimension) (1/2), ‖ξ‖ = 1 →
      ξ ∉ ProjectionConeTransversality.cone (secondProjection dimension) γ := by
  intro ξ plus unit minus
  have zero := cones_meet_zero dimension nonneg small plus minus
  rw [zero, norm_zero] at unit
  exact zero_ne_one unit

theorem diagonal_adjoint_apply (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (U : X ≃L[ℝ] X) (S : Y ≃L[ℝ] Y) (z : X × Y) :
    (diagonal dimension U S).toContinuousLinearMap.adjoint (equiv dimension z) =
      equiv dimension (U.toContinuousLinearMap.adjoint z.1, S.toContinuousLinearMap.adjoint z.2) := by
  apply ext_inner_left ℝ
  intro w
  obtain ⟨v, rfl⟩ := (equiv dimension).surjective w
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (diagonal dimension U S (equiv dimension v)) (equiv dimension z) = _
  rw [diagonal_apply, inner_map, inner_map, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem adjoint_rate_component_bounds (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (U : X ≃L[ℝ] X) (S : Y ≃L[ℝ] Y) (a : ℝ)
    (stable : ‖S.toContinuousLinearMap‖ ≤ a) (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ a) :
    (∀ v, ‖firstProjection dimension v‖ ≤
      a * ‖firstProjection dimension ((diagonal dimension U S).toContinuousLinearMap.adjoint v)‖) ∧
    (∀ v, ‖secondProjection dimension ((diagonal dimension U S).toContinuousLinearMap.adjoint v)‖ ≤
      a * ‖secondProjection dimension v‖) := by
  have undo (x : X) : U.symm.toContinuousLinearMap.adjoint
      (U.toContinuousLinearMap.adjoint x) = x := by
    have identity : U.symm.toContinuousLinearMap.adjoint.comp U.toContinuousLinearMap.adjoint =
        ContinuousLinearMap.id ℝ X := by
      rw [← ContinuousLinearMap.adjoint_comp]
      rw [show U.toContinuousLinearMap.comp U.symm.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ X from by ext v; exact U.apply_symm_apply v]
      exact ContinuousLinearMap.adjoint_id
    exact congrArg (fun A : X →L[ℝ] X => A x) identity
  constructor
  · intro v
    obtain ⟨z, rfl⟩ := (equiv dimension).surjective v
    rw [firstProjection_apply, diagonal_adjoint_apply, firstProjection_apply,
      norm_first_axis, norm_first_axis]
    have estimate := U.symm.toContinuousLinearMap.adjoint.le_opNorm
      (U.toContinuousLinearMap.adjoint z.1)
    rw [undo, ContinuousLinearMap.adjoint.norm_map] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right unstable (norm_nonneg _))
  · intro v
    obtain ⟨z, rfl⟩ := (equiv dimension).surjective v
    rw [secondProjection_apply, diagonal_adjoint_apply, secondProjection_apply,
      norm_second_axis, norm_second_axis]
    have estimate := S.toContinuousLinearMap.adjoint.le_opNorm z.2
    rw [ContinuousLinearMap.adjoint.norm_map] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right stable (norm_nonneg _))

theorem adjoint_half_polarization (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (U : X ≃L[ℝ] X) (S : Y ≃L[ℝ] Y) (q : ℝ)
    (positive : 0 < q) (contracting : q < 1)
    (stable : ‖S.toContinuousLinearMap‖ ≤ q) (unstable : ‖U.symm.toContinuousLinearMap‖ ≤ q)
    (B : E →L[ℝ] E)
    (close : ‖B - (diagonal dimension U S).toContinuousLinearMap‖ ≤
      ProjectionConeRateMargin.tolerance q)
    (v : E) (nonzero : v ≠ 0)
    (outside : v ∉ interior
      (ProjectionConeTransversality.cone (firstProjection dimension) (1/2))) :
    B.adjoint v ≠ 0 ∧ B.adjoint v ∈ interior
      (ProjectionConeTransversality.cone (secondProjection dimension) (narrowOpening q)) := by
  obtain ⟨_, narrowNonneg, _, _, _, _, positiveTol, gap⟩ := opening_bounds positive contracting
  obtain ⟨lower, upper⟩ := adjoint_rate_component_bounds dimension U S q stable unstable
  have adjointClose : ‖B.adjoint - (diagonal dimension U S).toContinuousLinearMap.adjoint‖ ≤
      ProjectionConeRateMargin.tolerance q := by
    rw [← map_sub, ContinuousLinearMap.adjoint.norm_map]
    exact close
  exact ProjectionConeSourceRateMargin.strict_action_of_source_gap
    (firstProjection dimension) (secondProjection dimension)
    (diagonal dimension U S).toContinuousLinearMap.adjoint B.adjoint q 2 (narrowOpening q)
    (ProjectionConeRateMargin.tolerance q) positive (by norm_num) narrowNonneg positiveTol.le gap
    (fun w => (add_comm _ _).trans (projections_add dimension w))
    (projection_bounds dimension).1 (projection_bounds dimension).2 lower upper adjointClose v nonzero
    (outside_half_mem_second dimension v outside)

end LeanShared.OneStepConePolarization
