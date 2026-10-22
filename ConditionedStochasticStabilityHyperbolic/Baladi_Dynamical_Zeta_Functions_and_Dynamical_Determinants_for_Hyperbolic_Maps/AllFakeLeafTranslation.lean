module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafImageTransport
public import LeanShared.Analysis.FakeLeafLinearImage
public import Mathlib.Topology.Homeomorph.Lemmas
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
import all LeanShared.Analysis.FakeLeafGraph

/-! Translation of actual induced leaf volume. A translation is a global C¹ diffeomorphism with
identity differential, so the exact nonlinear transport of induced leaf volume has tangent
Jacobian one: the volume of a translated embedded leaf is the translated volume, and the
translate of an admissible fake leaf is again an admissible fake leaf. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set MeasureTheory
open scoped ENNReal
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private abbrev shift (z : E) : OpenPartialHomeomorph E E :=
  (Homeomorph.addRight z).toOpenPartialHomeomorph

private theorem shift_forward (z : E) : ContDiffOn ℝ 1 (shift z) (shift z).source :=
  (contDiff_id.add contDiff_const).contDiffOn

private theorem shift_backward (z : E) : ContDiffOn ℝ 1 (shift z).symm (shift z).target := by
  have : ⇑(shift z).symm = fun x => x + -z := funext fun _ => rfl
  rw [this]
  exact (contDiff_id.add contDiff_const).contDiffOn

private theorem translate_slope {U : Submodule ℝ E} {Γ : Set E} {L : ℝ}
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ, ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖)
    (z : E) : ∀ x ∈ (fun x => x + z) '' Γ, ∀ y ∈ (fun x => x + z) '' Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖ := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [add_sub_add_right_eq_sub]
  exact slope x hx y hy

private theorem shift_density (z : E) (p : Submodule ℝ E) (y : E) :
    ENNReal.ofReal (((fderiv ℝ (shift z) y).toLinearMap.domRestrict p).normDet) = 1 := by
  have derivative : fderiv ℝ (shift z) y = ContinuousLinearMap.id ℝ E := by
    change fderiv ℝ (fun x => x + z) y = _
    rw [fderiv_add_const, fderiv_fun_id]
  rw [derivative]
  change ENNReal.ofReal ((LinearMap.id.comp p.subtype).normDet) = 1
  rw [LinearMap.id_comp, LinearMap.normDet_subtype, ENNReal.ofReal_one]

private theorem leafError_translate (C : Set E) (ds : ℕ) (Γ : Set E) (z : E) :
    FakeLeafGeometry.leafError C ds ((fun x => x + z) '' Γ) = FakeLeafGeometry.leafError C ds Γ := by
  unfold FakeLeafGeometry.leafError
  congr 1
  ext r
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hne, rfl⟩
    exact ⟨x, hx, y, hy, fun h => hne (by rw [h]), by rw [add_sub_add_right_eq_sub]⟩
  · rintro ⟨x, hx, y, hy, hne, rfl⟩
    exact ⟨x + z, ⟨x, hx, rfl⟩, y + z, ⟨y, hy, rfl⟩, fun h => hne (add_right_cancel h),
      by rw [add_sub_add_right_eq_sub]⟩

/-- The induced volume of a translated embedded leaf is the translated induced volume. -/
theorem C1Embedded.translation_volume {U : Submodule ℝ E} {Γ : Set E} [Nonempty Γ]
    (embedded : C1Embedded U Γ) (μ : Measure U) [μ.IsAddHaarMeasure] {L : ℝ} (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ, ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖)
    (a : E) :
    (EmbeddedSubmanifoldVolume.volume U μ Γ).map (fun x => x + a) =
      EmbeddedSubmanifoldVolume.volume U μ ((fun x => x + a) '' Γ) := by
  have transport := embedded.image_tangent_volume μ hL hL slope (shift a) (subset_univ _)
    (shift_forward a) (shift_backward a) (translate_slope slope a)
  simp only [shift_density, one_mul] at transport
  change _ = EmbeddedSubmanifoldVolume.volume U μ ((fun x => x + a) '' Γ) at transport
  rw [← transport, embedded.graph_parametric_volume μ hL slope]
  have graphMeasurable : Measurable (ConeGraphGeometry.graphPoint U
      (FakeLeafGraph.heightExtension U Γ hL slope)) := by
    change Measurable (fun u : U => (u : E) + (FakeLeafGraph.heightExtension U Γ hL slope u : E))
    exact continuous_subtype_val.measurable.add (continuous_subtype_val.measurable.comp
      (FakeLeafGraph.heightExtension_measurable U Γ hL slope embedded.measurableSet))
  rw [Measure.map_map (measurable_add_const a) graphMeasurable]
  rfl

/-- The translate of a nonempty admissible fake leaf is an admissible fake leaf carrying the
translated induced volume. -/
theorem exists_translated_leaf (U : Submodule ℝ E) {C : Set E} (cone : ConeData U C)
    (μ : Measure U) [μ.IsAddHaarMeasure] (Γ : Index U C) [Nonempty Γ.val] (a : E) :
    ∃ image : Index U C, image.val = (fun x => x + a) '' Γ.val ∧
      (EmbeddedSubmanifoldVolume.volume U μ Γ.val).map (fun x => x + a) =
        EmbeddedSubmanifoldVolume.volume U μ image.val := by
  have hL := (slope_positive U C cone).le
  have slope := slope_bound U C cone Γ
  refine ⟨⟨(fun x => x + a) '' Γ.val, Γ.property.1.image_local_diffeomorphism hL slope (shift a)
      (subset_univ _) (shift_forward a) (shift_backward a),
    (leafError_translate C _ Γ.val a).trans Γ.property.2⟩, rfl, ?_⟩
  exact Γ.property.1.translation_volume μ hL slope a

end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
