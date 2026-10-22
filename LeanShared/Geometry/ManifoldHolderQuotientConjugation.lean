module
public import LeanShared.Geometry.ManifoldHolderQuotient
public import LeanShared.Geometry.BoundedHolderConjugation

/-! Complex conjugation on the constructed lower-regularity manifold space
(finite product of Euclidean little Hölder chart spaces modulo the
reconstruction kernel). Pointwise conjugation preserves each Euclidean little
Hölder space (by smooth-core conjugation and density), commutes with the
literal chart reconstruction, hence descends to the quotient, with
`physical (J v) = star (physical v)` and `‖J v‖ ≤ ‖v‖`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set
open scoped Manifold ContDiff BoundedContinuousFunction ComplexConjugate

namespace LeanShared.EuclideanSmoothHolderCore
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {V : Set E} (hV : IsCompact (closure V))
  {b : ℝ} (hb : 0 < b) (hb1 : b < 1)

private theorem graph_core_conjugation (c : SmoothSupportedManifoldCore.core (E := E) V) :
    BoundedHolderSpace.conjugate E b (core hV hb hb1 c) =
      core hV hb hb1 (SmoothSupportedManifoldCore.conjugate V c) := by
  apply BoundedHolderSpace.physical_injective E b
  ext x
  rw [BoundedHolderSpace.conjugate_physical]
  rfl

theorem mapsTo_space (v : space hV hb hb1) :
    BoundedHolderSpace.conjugate E b v.val ∈ space hV hb hb1 := by
  refine (smooth_dense hV hb hb1).induction_on
    (p := fun z => BoundedHolderSpace.conjugate E b z.val ∈ space hV hb hb1) v
    (((core hV hb hb1).range.isClosed_topologicalClosure).preimage
      ((BoundedHolderSpace.conjugate E b).continuous.comp continuous_subtype_val)) ?_
  intro c
  change BoundedHolderSpace.conjugate E b (core hV hb hb1 c) ∈ _
  rw [graph_core_conjugation]
  exact (core hV hb hb1).range.le_topologicalClosure ⟨_, rfl⟩

@[expose] def conjugateLinear : space hV hb hb1 →ₗ[ℝ] space hV hb hb1 where
  toFun v := ⟨BoundedHolderSpace.conjugate E b v.val, mapsTo_space hV hb hb1 v⟩
  map_add' a c := Subtype.ext ((BoundedHolderSpace.conjugate E b).map_add a.val c.val)
  map_smul' r a := Subtype.ext ((BoundedHolderSpace.conjugate E b).map_smul r a.val)

@[expose] def conjugate : space hV hb hb1 →L[ℝ] space hV hb hb1 :=
  (conjugateLinear hV hb hb1).mkContinuous 1 (fun v => by
    change ‖BoundedHolderSpace.conjugate E b v.val‖ ≤ 1 * ‖v.val‖
    rw [BoundedHolderSpace.conjugate_norm, one_mul])

theorem conjugate_norm (v : space hV hb hb1) : ‖conjugate hV hb hb1 v‖ = ‖v‖ :=
  BoundedHolderSpace.conjugate_norm E b v.val

theorem physical_conjugate (v : space hV hb hb1) (x : E) :
    physical hV hb hb1 (conjugate hV hb hb1 v) x = star (physical hV hb hb1 v x) :=
  BoundedHolderSpace.conjugate_physical E b v.val x

end LeanShared.EuclideanSmoothHolderCore

namespace LeanShared.ManifoldHolderQuotient
variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]
  [Fintype I] {e : I → OpenPartialHomeomorph M E} {K : I → Set E} {V : Set M}
  (d : ChartSmoothingRegions.Data e K V) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)

local instance coordinatesNormed' : NormedAddCommGroup (Coordinates d hb hb1) := inferInstance
local instance coordinatesSeminormed' : SeminormedAddCommGroup (Coordinates d hb hb1) :=
  (coordinatesNormed' d hb hb1).toSeminormedAddCommGroup

/-- Componentwise conjugation of the chart coordinates. -/
@[expose] def coordinatesConjugate : Coordinates d hb hb1 →L[ℝ] Coordinates d hb hb1 :=
  ContinuousLinearMap.pi fun i =>
    (EuclideanSmoothHolderCore.conjugate (d.compact_closure i) hb hb1).comp
      (ContinuousLinearMap.proj i)

theorem coordinatesConjugate_apply (z : Coordinates d hb hb1) (i : I) :
    coordinatesConjugate d hb hb1 z i =
      EuclideanSmoothHolderCore.conjugate (d.compact_closure i) hb hb1 (z i) := rfl

theorem norm_coordinatesConjugate (z : Coordinates d hb hb1) :
    ‖coordinatesConjugate d hb hb1 z‖ = ‖z‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    rw [coordinatesConjugate_apply, EuclideanSmoothHolderCore.conjugate_norm]
    exact norm_le_pi_norm z i
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    have h := norm_le_pi_norm (coordinatesConjugate d hb hb1 z) i
    rw [coordinatesConjugate_apply, EuclideanSmoothHolderCore.conjugate_norm] at h
    exact h

theorem function_star (f : OpenPartialHomeomorph M E) (h : E → ℂ) (x : M) :
    SupportedChartExtension.function f (fun y => star (h y)) x =
      star (SupportedChartExtension.function f h x) := by
  classical
  unfold SupportedChartExtension.function
  split_ifs
  · rfl
  · exact (star_zero ℂ).symm

theorem reconstruction_apply' (z : Coordinates d hb hb1) (x : M) :
    reconstruction d hb hb1 z x = ∑ i, SupportedChartExtension.function (e i)
      (fun y => EuclideanSmoothHolderCore.physical (d.compact_closure i) hb hb1 (z i) y) x := by
  simp only [reconstruction, ContinuousLinearMap.comp_apply,
    FiniteHolderChartPatching.reconstruction_apply]
  rfl

theorem reconstruction_conjugate (z : Coordinates d hb hb1) :
    reconstruction d hb hb1 (coordinatesConjugate d hb hb1 z) = star (reconstruction d hb hb1 z) := by
  ext x
  rw [BoundedContinuousFunction.star_apply, reconstruction_apply', reconstruction_apply',
    star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← function_star]
  rfl

theorem exists_conjugate (v : Space d hb hb1) :
    ∃ w : Space d hb hb1, physical d hb hb1 w = star (physical d hb hb1 v) := by
  obtain ⟨z, rfl⟩ := BanachFunctionQuotient.quotient_surjective (𝕜 := ℂ)
    (H := Coordinates d hb hb1) (X := M) (F := ℂ) (reconstruction d hb hb1) v
  exact ⟨quotient d hb hb1 (coordinatesConjugate d hb hb1 z), by
    rw [physical_quotient, reconstruction_conjugate]
    rfl⟩

/-- Pointwise conjugation on the lower-regularity space. -/
@[expose] def conjugateFun (v : Space d hb hb1) : Space d hb hb1 :=
  (exists_conjugate d hb hb1 v).choose

theorem physical_conjugateFun (v : Space d hb hb1) :
    physical d hb hb1 (conjugateFun d hb hb1 v) = star (physical d hb hb1 v) :=
  (exists_conjugate d hb hb1 v).choose_spec

theorem conjugateFun_quotient (z : Coordinates d hb hb1) :
    conjugateFun d hb hb1 (quotient d hb hb1 z) =
      quotient d hb hb1 (coordinatesConjugate d hb hb1 z) := by
  apply physical_injective d hb hb1
  rw [physical_conjugateFun, physical_quotient, physical_quotient, reconstruction_conjugate]

theorem norm_conjugateFun_le (v : Space d hb hb1) : ‖conjugateFun d hb hb1 v‖ ≤ ‖v‖ := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨z, hz, small⟩ := Submodule.Quotient.norm_mk_lt (S := (reconstruction d hb hb1).ker) v hε
  have hv : v = quotient d hb hb1 z := hz.symm
  have key : conjugateFun d hb hb1 v = quotient d hb hb1 (coordinatesConjugate d hb hb1 z) := by
    rw [hv, conjugateFun_quotient]
  rw [key]
  calc ‖quotient d hb hb1 (coordinatesConjugate d hb hb1 z)‖
      ≤ ‖coordinatesConjugate d hb hb1 z‖ := Submodule.Quotient.norm_mk_le _ _
    _ = ‖z‖ := norm_coordinatesConjugate d hb hb1 z
    _ < ‖v‖ + ε := small

@[expose] def conjugateLinear : Space d hb hb1 →ₗ[ℝ] Space d hb hb1 where
  toFun := conjugateFun d hb hb1
  map_add' v w := by
    apply physical_injective d hb hb1
    rw [map_add, physical_conjugateFun, physical_conjugateFun, physical_conjugateFun, map_add,
      star_add]
  map_smul' r v := by
    apply physical_injective d hb hb1
    rw [RingHom.id_apply, physical_conjugateFun, ContinuousLinearMap.map_smul_of_tower,
      ContinuousLinearMap.map_smul_of_tower, physical_conjugateFun, star_smul, star_trivial]

/-- The continuous real-linear conjugation. -/
@[expose] def conjugate : Space d hb hb1 →L[ℝ] Space d hb hb1 :=
  (conjugateLinear d hb hb1).mkContinuous 1 (fun v => by
    rw [one_mul]
    exact norm_conjugateFun_le d hb hb1 v)

theorem physical_conjugate (v : Space d hb hb1) (x : M) :
    physical d hb hb1 (conjugate d hb hb1 v) x = star (physical d hb hb1 v x) := by
  change physical d hb hb1 (conjugateFun d hb hb1 v) x = _
  rw [physical_conjugateFun, BoundedContinuousFunction.star_apply]

end LeanShared.ManifoldHolderQuotient
