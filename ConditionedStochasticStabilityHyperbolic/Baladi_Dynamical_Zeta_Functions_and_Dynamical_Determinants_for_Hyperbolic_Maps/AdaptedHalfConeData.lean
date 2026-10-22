module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
public import LeanShared.Analysis.ProjectionConeRadialMargin
public import LeanShared.Analysis.OrthogonalDiagonalConeBounds
public import LeanShared.Geometry.OrthogonalProductAxisPlanes

/-! The plus half frequency cone around the stable axis, with the unstable
axis as leaf plane, satisfies every fake-leaf cone requirement: it is closed,
conic, transversal to the unstable plane, and contains the stable plane as an
admissible normal plane. -/
public noncomputable section
open Set
namespace ConditionedStochasticStabilityHyperbolic.AdaptedHalfConeData
open LeanShared LeanShared.OrthogonalProductCoordinates AllFakeLeafModel
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

theorem halfConeData (dimension : Module.finrank ℝ (X×Y) = Module.finrank ℝ E)
    (positiveY : 0 < Module.finrank ℝ Y) :
    ConeData (firstPlane dimension)
      (ProjectionConeTransversality.cone (firstProjection dimension) (1/2)) where
  closed := ProjectionConeRadialMargin.closed _ _
  scale := fun _ hr _ hv => ProjectionConeRadialMargin.smul_mem _ hr hv
  transverse := by
    intro v cone plane
    have fixed : firstProjection dimension v = v := by
      rw [← firstPlane_projection]
      exact Submodule.starProjection_eq_self_iff.mpr plane
    change ‖firstProjection dimension v‖ ≤ (1/2) * ‖v - firstProjection dimension v‖ at cone
    rw [fixed, sub_self, norm_zero, mul_zero] at cone
    exact norm_eq_zero.mp (le_antisymm cone (norm_nonneg _))
  stable_positive := by
    rw [← secondPlane_eq_orthogonal, secondPlane_dimension]
    exact positiveY
  normal_planes := by
    refine ⟨secondPlane dimension, ?_, ?_⟩
    · intro v member
      have zero : firstProjection dimension v = 0 := by
        rw [← firstPlane_projection]
        apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
        rw [← secondPlane_eq_orthogonal]
        exact member
      change ‖firstProjection dimension v‖ ≤ (1/2) * ‖v - firstProjection dimension v‖
      rw [zero, norm_zero]
      positivity
    · rw [← secondPlane_eq_orthogonal]

end ConditionedStochasticStabilityHyperbolic.AdaptedHalfConeData
