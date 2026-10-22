module
public import LeanShared.Dynamics.HyperbolicNativeTransportWindows
public import LeanShared.Geometry.CompactUniformCenteredCharts
import all LeanShared.Geometry.CompactUniformCenteredCharts

/-! One finite compact neighborhood cover and one native norm factor work
for EVERY requested projection error. The error-dependent distance threshold
is chosen afterwards, allowing a noncircular hyperbolic block construction. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Filter IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle

set_option maxHeartbeats 1600000 in
theorem HyperbolicData.exists_uniform_native_transport_windows
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    :
    ∃ centers : Finset Λ, ∃ patch : Λ → Set Λ,
      (∀ i, IsCompact (patch i)) ∧ (univ : Set Λ) ⊆ ⋃ i ∈ centers, interior (patch i) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ < 1 → ∃ η : ℝ, 0 < η ∧
      ∀ i ∈ centers, ∀ x ∈ patch i, ∀ y : Λ, dist x y < η →
        let e := trivializationAt E (fun z : M => TangentSpace (𝓘(ℝ, E)) z) i.val
        x.val ∈ e.baseSet ∧ y.val ∈ e.baseSet ∧
        ∃ R : TangentSpace (𝓘(ℝ, E)) x.val ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) y.val,
          (∀ v, h.projection y.val (R v) = R (h.projection x.val v)) ∧
          ‖R.toContinuousLinearMap‖ ≤ C ^ 2 * (1 + θ) ∧
          ‖R.symm.toContinuousLinearMap‖ ≤ C ^ 2 / (1 - θ) ∧
          ‖(e.continuousLinearMapAt ℝ y.val).comp
            (R.toContinuousLinearMap.comp (e.symmL ℝ x.val)) - ContinuousLinearMap.id ℝ E‖ < θ := by
  classical
  let _ : CompactSpace Λ := isCompact_iff_compactSpace.mp h.compact
  let fibers := fun x : M => TangentSpace (𝓘(ℝ, E)) x
  choose W openW member C positiveC transport using
    fun i : Λ => h.exists_native_transport_windows i
  let U (i : Λ) : Set Λ := W i ∩ Subtype.val ⁻¹' (trivializationAt E fibers i.val).baseSet
  have openU (i : Λ) : IsOpen (U i) := (openW i).inter
    ((trivializationAt E fibers i.val).open_baseSet.preimage continuous_subtype_val)
  have memberU (i : Λ) : i ∈ U i :=
    ⟨member i,FiberBundle.mem_baseSet_trivializationAt E fibers i.val⟩
  have neighborhoods (i : Λ) : ∃ P : Set Λ, P ∈ 𝓝 i ∧ IsClosed P ∧ P ⊆ U i :=
    exists_mem_nhds_isClosed_subset ((openU i).mem_nhds (memberU i))
  choose patch neighborhood closed subset using neighborhoods
  have interiorMember (i : Λ) : i ∈ interior (patch i) := mem_interior_iff_mem_nhds.mpr (neighborhood i)
  obtain ⟨centers,covers⟩ := (isCompact_univ : IsCompact (univ : Set Λ)).elim_finite_subcover
    (fun i : Λ => interior (patch i)) (fun _ => isOpen_interior)
    (fun i _ => mem_iUnion.mpr ⟨i,interiorMember i⟩)
  let bound := 1 + ∑ i ∈ centers, C i
  have positiveBound : 0 < bound := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun i _ => (positiveC i).le))
  have bounded (i : Λ) (hi : i ∈ centers) : C i ≤ bound :=
    (Finset.single_le_sum (fun j _ => (positiveC j).le) hi).trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨centers,patch,fun i => (closed i).isCompact,covers,
    bound,positiveBound,fun θ positive small => ?_⟩
  have windows (i : Λ) := transport i θ positive small (patch i) (closed i).isCompact
    (fun x hx => (subset i hx).1)
  choose η positiveη transportAt using windows
  have domainWindows (i : Λ) := CompactNearDiagonalContinuity.exists_radius (patch i)
    (Subtype.val ⁻¹' (trivializationAt E fibers i.val).baseSet) (closed i).isCompact
    ((trivializationAt E fibers i.val).open_baseSet.preimage continuous_subtype_val)
    (fun x hx => (subset i hx).2) id continuousOn_id 1 zero_lt_one
  choose δ positiveδ domainAt using domainWindows
  obtain ⟨radius,positiveRadius,common⟩ := CompactUniformCenteredCharts.common_positive centers
    (fun i => min (η i) (δ i)) (fun i _ => lt_min (positiveη i) (positiveδ i))
  refine ⟨radius,positiveRadius,fun i hi x hx y near => ?_⟩
  have localNear : dist x y < min (η i) (δ i) := near.trans_le (common i hi)
  have hy := (domainAt i x hx y (localNear.trans_le (min_le_right _ _))).1
  obtain ⟨R,commutes,normR,inverseR,closeR⟩ := transportAt i x hx y
    (localNear.trans_le (min_le_left _ _))
  have square : C i ^ 2 ≤ bound ^ 2 := by nlinarith [positiveC i,bounded i hi]
  refine ⟨(subset i hx).2,hy,R,commutes,?_,?_,closeR⟩
  · exact normR.trans (mul_le_mul_of_nonneg_right square (by linarith))
  · exact inverseR.trans (div_le_div_of_nonneg_right square (sub_pos.mpr small).le)

end LeanShared.HyperbolicBasicSet
