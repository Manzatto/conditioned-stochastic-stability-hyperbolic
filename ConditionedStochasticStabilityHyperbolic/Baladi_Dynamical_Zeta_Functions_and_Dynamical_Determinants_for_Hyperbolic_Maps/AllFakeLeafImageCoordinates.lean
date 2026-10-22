module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafImageImmersion
public import LeanShared.Analysis.FakeLeafProjectionPairing
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
import all LeanShared.Analysis.FakeLeafGraph

/-! The coordinate change between a genuine leaf and its nonlinear image is
constructed from their actual global graph charts and the actual local
homeomorphism. -/
public noncomputable section
open Set
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem C1Embedded.exists_image_coordinates {U : Submodule ℝ E} {Γ : Set E}
    [Nonempty Γ] (source : C1Embedded U Γ) {LS LT : ℝ} (hLS : 0 ≤ LS) (hLT : 0 ≤ LT)
    (sourceSlope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ LS * ‖U.starProjection (x-y)‖)
    (F : OpenPartialHomeomorph E E) (inside : Γ ⊆ F.source)
    (forward : ContDiffOn ℝ 1 F F.source) (backward : ContDiffOn ℝ 1 F.symm F.target)
    (targetSlope : ∀ x ∈ F '' Γ, ∀ y ∈ F '' Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ LT * ‖U.starProjection (x-y)‖) :
    ∃ h : OpenPartialHomeomorph U U,
      h.source = FakeLeafGraph.parameterDomain U Γ ∧
      h.target = FakeLeafGraph.parameterDomain U (F '' Γ) ∧
      ContDiffOn ℝ 1 h h.source ∧
      ∀ u ∈ h.source,
        F (ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ hLS sourceSlope) u) =
        ConeGraphGeometry.graphPoint U
          (FakeLeafGraph.heightExtension U (F '' Γ) hLT targetSlope) (h u) := by
  let image := F.homeomorphOfImageSubsetSource inside rfl
  let : Nonempty (F '' Γ) := ⟨image (Classical.choice ‹Nonempty Γ›)⟩
  have target := source.image_local_diffeomorphism hLS sourceSlope F inside forward backward
  let eS := FakeLeafProjectionChart.chart U Γ hLS sourceSlope (source.projection_open hLS sourceSlope)
  let eT := FakeLeafProjectionChart.chart U (F '' Γ) hLT targetSlope (target.projection_open hLT targetSlope)
  let h := eS.symm.trans (image.toOpenPartialHomeomorph.trans eT)
  have sourceDomain : h.source = FakeLeafGraph.parameterDomain U Γ := by
    change FakeLeafGraph.parameterDomain U Γ ∩ eS.symm ⁻¹'
      (univ ∩ image.toOpenPartialHomeomorph ⁻¹' univ) = _
    simp only [preimage_univ, inter_univ]
  have targetDomain : h.target = FakeLeafGraph.parameterDomain U (F '' Γ) := by
    simp only [h, OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
      preimage_univ, inter_univ]
    change _ ∩ _ ⁻¹' univ = _
    simp only [preimage_univ, inter_univ]
    rfl
  let gS := ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U Γ hLS sourceSlope)
  let gT := ConeGraphGeometry.graphPoint U (FakeLeafGraph.heightExtension U (F '' Γ) hLT targetSlope)
  have sourceInverse (u : U) (hu : u ∈ h.source) : (eS.symm u : E) = gS u :=
    FakeLeafProjectionChart.ambient_inverse_eq_graph U Γ hLS sourceSlope u (sourceDomain ▸ hu)
  have value (u : U) (hu : u ∈ h.source) : h u = U.orthogonalProjectionOnto (F (gS u)) := by
    change U.orthogonalProjectionOnto (F (eS.symm u : E)) = _
    rw [sourceInverse u hu]
  refine ⟨h, sourceDomain, targetDomain, ?_, ?_⟩
  · have graphRegular : ContDiffOn ℝ 1 gS h.source := by
      rw [sourceDomain]
      exact U.subtypeL.contDiff.contDiffOn.add
        (Uᗮ.subtypeL.contDiff.comp_contDiffOn (source.heightExtension_contDiffOn hLS sourceSlope))
    have imageSource : MapsTo gS h.source F.source := by
      intro u hu
      rw [← sourceInverse u hu]
      exact inside (eS.symm u).property
    exact ((U.orthogonalProjectionOnto.contDiff.comp_contDiffOn
      (forward.comp graphRegular imageSource)).congr (fun u hu => value u hu))
  · intro u hu
    have targetInverse := FakeLeafProjectionChart.ambient_inverse_eq_graph U (F '' Γ)
      hLT targetSlope (h u) (targetDomain ▸ h.map_source hu)
    have targetInverse' : (eT.symm (h u) : E) = gT (h u) := targetInverse
    have left := congrArg Subtype.val (eT.left_inv
      (show image (eS.symm u) ∈ eT.source by trivial))
    change (eT.symm (h u) : E) = F (eS.symm u : E) at left
    rw [targetInverse', sourceInverse u hu] at left
    exact left.symm
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
