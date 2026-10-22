module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafImageImmersion
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafCharts
public import LeanShared.Analysis.StrictInverseAdjointCone
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel

/-! A strict deterministic cone map selects a neighborhood on which genuine
nonlinear local diffeomorphisms map the entire actual fake-leaf family into
the target family. Both C¹ immersion and the full secant condition are proved. -/
public noncomputable section
open Set
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_nonlinear_image_radius (U : Submodule ℝ E) {C D : Set E}
    (sourceCone : ConeData U C) (targetCone : ConeData U D) (A : E ≃L[ℝ] E)
    (strict : ∀ v ∈ C ∩ Metric.sphere (0 : E) 1,
      FakeLeafLinearImage.adjointEquiv A.symm v ∈ interior D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (F : OpenPartialHomeomorph E E) (s : Set E),
      Convex ℝ s → s ⊆ F.source →
      ContDiffOn ℝ 1 F F.source → ContDiffOn ℝ 1 F.symm F.target →
      (∀ x ∈ s, ‖fderiv ℝ F x - A.toContinuousLinearMap‖ ≤ δ) →
      ∀ Γ : Index U C, Γ.val ⊆ s → ∃ image : Index U D, image.val = F '' Γ.val := by
  have zeroD : (0 : E) ∈ D := by
    obtain ⟨P, hp⟩ := targetCone.normal_planes
    exact hp.1 P.zero_mem
  obtain ⟨δ, positive, imageFake⟩ := StrictInverseAdjointCone.exists_image_radius
    sourceCone.stable_positive sourceCone.normal_planes sourceCone.closed sourceCone.scale
    zeroD targetCone.scale A strict
  refine ⟨δ, positive, fun F s convex inside forward backward comparison Γ sourceInside => ?_⟩
  have fake : FakeLeafGeometry.leafError D (Module.finrank ℝ Uᗮ) (F '' Γ.val) = 0 :=
    imageFake F s convex (fun x hx => ((forward.differentiableOn one_ne_zero) x
      (inside hx)).differentiableAt (F.open_source.mem_nhds (inside hx)))
      comparison Γ.val sourceInside Γ.property.2
  have embedded : C1Embedded U (F '' Γ.val) := by
    by_cases nonempty : Nonempty Γ.val
    · let : Nonempty Γ.val := nonempty
      exact Γ.property.1.image_local_diffeomorphism (slope_positive U C sourceCone).le
        (slope_bound U C sourceCone Γ) F (sourceInside.trans inside) forward backward
    · have empty : Γ.val = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact nonempty ⟨⟨x, hx⟩⟩
      simpa only [empty, image_empty] using embedded_empty U
  exact ⟨⟨F '' Γ.val, embedded, fake⟩, rfl⟩
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
