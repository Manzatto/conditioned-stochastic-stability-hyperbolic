module
public import LeanShared.Dynamics.HyperbolicUniformNativeTransport
public import LeanShared.Dynamics.HyperbolicSplittingTransport
public import LeanShared.Dynamics.HyperbolicTangentBlockEquivalences
public import Mathlib.Tactic.FieldSimp
public import LeanShared.Geometry.TangentChartTrivialization

/-! A complete CONSTRUCTED pseudo-reference output: one finite coherent
chart index, its actual compact core patches and source margins, native norm
bound, block length, and all subsequent error-dependent transport windows.
No chart, block, splitting transport or contraction packet is an input. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle

structure PseudoReferenceGeometry
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ) where
  centers : Finset Λ
  index : Λ → Λ
  index_mem : ∀ x, index x ∈ centers
  finite_index : (Set.range index).Finite
  patch : Λ → Set Λ
  compact_patch : ∀ i, IsCompact (patch i)
  selected_patch : ∀ x, x ∈ patch (index x)
  chart_source : ∀ i ∈ centers, ∀ x ∈ patch i, x.val ∈ (chartAt E i.val).source
  nativeBound : ℝ
  nativeBound_positive : 0 < nativeBound
  blockLength : ℕ
  block_positive : 0 < blockLength
  produce : ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∃ η : ℝ, 0 < η ∧
      ∀ x y : Λ, dist ((T ^ blockLength) x.val) y.val < η →
        let e := trivializationAt E (fun z : M => TangentSpace (𝓘(ℝ, E)) z) (index y).val
        y.val ∈ e.baseSet ∧ (T ^ blockLength) x.val ∈ e.baseSet ∧
        ∃ R : TangentSpace (𝓘(ℝ, E)) ((T ^ blockLength) x.val) ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) y.val,
        ∃ S : h.stable x.val ≃L[ℝ] h.stable y.val,
        ∃ U : h.unstable x.val ≃L[ℝ] h.unstable y.val,
          ‖R.toContinuousLinearMap‖ ≤ nativeBound ∧ ‖R.symm.toContinuousLinearMap‖ ≤ nativeBound ∧
          ‖S.toContinuousLinearMap‖ ≤ 1 / 4 ∧ ‖U.symm.toContinuousLinearMap‖ ≤ 1 / 4 ∧
          (∀ v, (S v).val = R (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (T ^ blockLength : M ≃ₜ M) x.val v.val)) ∧
          (∀ v, (U v).val = R (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (T ^ blockLength : M ≃ₜ M) x.val v.val)) ∧
          ‖(e.continuousLinearMapAt ℝ ((T ^ blockLength) x.val)).comp
            (R.symm.toContinuousLinearMap.comp (e.symmL ℝ y.val)) - ContinuousLinearMap.id ℝ E‖ < θ

set_option maxHeartbeats 3200000 in
theorem HyperbolicData.exists_pseudo_reference_geometry
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm) :
    Nonempty (PseudoReferenceGeometry h) := by
  classical
  obtain ⟨centers,patch,_compact,cover,C,positiveC,windows⟩ := h.exists_uniform_native_transport_windows
  have indices (y : Λ) : ∃ i, i ∈ centers ∧ y ∈ patch i := by
    obtain ⟨i,hi,member⟩ := mem_iUnion₂.mp (cover (mem_univ y))
    exact ⟨i,hi,interior_subset member⟩
  choose index memberIndex memberPatch using indices
  let B := 2 * C ^ 2 + 1
  have positiveB : 0 < B := by dsimp only [B]; positivity
  let κ := 1 / (4 * B)
  have positiveκ : 0 < κ := div_pos zero_lt_one (mul_pos (by norm_num) positiveB)
  obtain ⟨N,positiveN,blocks⟩ := h.exists_actual_tangent_blocks forward inverse κ positiveκ
  have product : B * κ = 1 / 4 := by
    dsimp only [κ]
    field_simp
  have preserves : MapsTo T Λ Λ := fun x hx => h.invariant ▸ mem_image_of_mem T hx
  have finiteIndex : (Set.range index).Finite := centers.finite_toSet.subset (by
    rintro _ ⟨y,rfl⟩
    exact memberIndex y)
  obtain ⟨halfRadius,positiveHalf,halfTransport⟩ := windows (1 / 2) (by norm_num) (by norm_num)
  have chartSource (i : Λ) (hi : i ∈ centers) (x : Λ) (hx : x ∈ patch i) :
      x.val ∈ (chartAt E i.val).source := by
    have base := (halfTransport i hi x hx x (by simpa only [dist_self] using positiveHalf)).1
    rwa [TangentChartTrivialization.baseSet] at base
  refine ⟨{
    centers := centers
    index := index
    index_mem := memberIndex
    finite_index := finiteIndex
    patch := patch
    compact_patch := _compact
    selected_patch := memberPatch
    chart_source := chartSource
    nativeBound := B
    nativeBound_positive := positiveB
    blockLength := N
    block_positive := positiveN
    produce := ?_ }⟩
  intro θ positiveθ smallθ
  have θlt : θ < 1 := by linarith
  obtain ⟨η,positiveη,transport⟩ := windows θ positiveθ θlt
  refine ⟨η,positiveη,fun x y near => ?_⟩
  have imageMember : (T ^ N) x.val ∈ Λ := by
    rw [DiffeomorphismIterates.coe_pow]
    exact preserves.iterate N x.property
  let image : Λ := ⟨(T ^ N) x.val,imageMember⟩
  have close : dist y image < η := by simpa only [Subtype.dist_eq,dist_comm] using near
  obtain ⟨source,target,R0,commutes,normR0,inverseR0,closeR0⟩ :=
    transport (index y) (memberIndex y) y (memberPatch y) image close
  have boundR : ‖R0.toContinuousLinearMap‖ ≤ B := normR0.trans (by
    dsimp only [B]
    nlinarith [sq_nonneg C])
  have boundInverse : ‖R0.symm.toContinuousLinearMap‖ ≤ B := inverseR0.trans (by
    apply (div_le_iff₀ (sub_pos.mpr θlt)).2
    dsimp only [B]
    nlinarith [sq_nonneg C])
  have inverseCommutes (v : TangentSpace (𝓘(ℝ, E)) image.val) :
      h.projection y.val (R0.symm v) = R0.symm (h.projection image.val v) := by
    apply R0.injective
    rw [← commutes,R0.apply_symm_apply,R0.apply_symm_apply]
  obtain ⟨S0,U0,stableBound,unstableBound,stableAction,unstableAction,_inverseAction⟩ := blocks x.val x.property
  obtain ⟨RS,RU,restrictedS,_restrictedInvS,_restrictedU,restrictedInvU,actionS,actionU⟩ :=
    h.exists_restricted_transport image y R0.symm inverseCommutes
  refine ⟨source,target,R0.symm,S0.trans RS,U0.trans RU,boundInverse,?_,?_,?_,?_,?_,?_⟩
  · simpa only [ContinuousLinearEquiv.symm_symm] using boundR
  · change ‖RS.toContinuousLinearMap.comp S0.toContinuousLinearMap‖ ≤ 1 / 4
    calc
      _ ≤ ‖RS.toContinuousLinearMap‖ * ‖S0.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ B * κ := mul_le_mul (restrictedS.trans boundInverse) stableBound (norm_nonneg S0.toContinuousLinearMap) positiveB.le
      _ = _ := product
  · change ‖U0.symm.toContinuousLinearMap.comp RU.symm.toContinuousLinearMap‖ ≤ 1 / 4
    calc
      _ ≤ ‖U0.symm.toContinuousLinearMap‖ * ‖RU.symm.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ κ * B := mul_le_mul unstableBound (restrictedInvU.trans boundR) (norm_nonneg RU.symm.toContinuousLinearMap) positiveκ.le
      _ = _ := by rw [mul_comm,product]
  · intro v
    change (RS (S0 v)).val = _
    rw [actionS,stableAction]
  · intro v
    change (RU (U0 v)).val = _
    rw [actionU,unstableAction]
  · simpa only [ContinuousLinearEquiv.symm_symm] using closeR0

end LeanShared.HyperbolicBasicSet
