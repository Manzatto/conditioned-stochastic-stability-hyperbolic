module
public import LeanShared.Dynamics.HyperbolicAdaptedEuclideanCones
public import LeanShared.Analysis.OneStepConePolarization
public import LeanShared.Analysis.ConstructedEnlargedConeSymbols
public import LeanShared.Analysis.EvenEnlargedConeSymbols

/-! Even original and enlarged cone cutoffs for the adapted Euclidean cones of a patch system:
the half cone around the first projection and the minus cone of the one-step opening are closed and
meet the unit sphere disjointly, so the constructed cutoffs exist; averaging with the reflection
makes the original angular symbol even. -/
public noncomputable section
open Set
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicAdaptedPatchSystem
open HyperbolicBasicSet ConstructedEnlargedConeSymbols
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

theorem projection_cone_closed {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : F →L[ℝ] F) (κ : ℝ) : IsClosed (ProjectionConeTransversality.cone P κ) :=
  isClosed_le (continuous_norm.comp P.continuous)
    (continuous_const.mul (continuous_norm.comp (continuous_id.sub P.continuous)))

/-- The even cone cutoffs of the adapted Euclidean model. -/
def PatchSystem.evenCutoffs (system : PatchSystem b) :
    Cutoffs (ProjectionConeTransversality.cone system.euclideanFirstProjection (1/2))
      (ProjectionConeTransversality.cone system.euclideanSecondProjection
        (OneStepConePolarization.minusOpening system.rate)) :=
  have bounds := OneStepConePolarization.opening_bounds system.rate_pos system.rate_lt_one
  EvenEnlargedConeSymbols.even
    (construct (projection_cone_closed _ _) (projection_cone_closed _ _)
      (OneStepConePolarization.half_minus_disjoint system.euclideanDimension bounds.2.2.2.2.2.1
        bounds.2.2.2.2.1))
    (EvenEnlargedConeSymbols.projection_cone_neg _ _)
    (EvenEnlargedConeSymbols.projection_cone_neg _ _)

theorem PatchSystem.evenCutoffs_even (system : PatchSystem b) (ξ : system.EuclideanModel) :
    system.evenCutoffs.original.toFun (-ξ) = system.evenCutoffs.original.toFun ξ :=
  EvenEnlargedConeSymbols.even_original _ _ _ ξ

end LeanShared.HyperbolicAdaptedPatchSystem
