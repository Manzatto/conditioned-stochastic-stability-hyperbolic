module
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.Homeomorph.Defs

/-! Uniform closeness to a homeomorphism controls every actual right inverse
through the modulus of continuity of the deterministic inverse. -/
public section
namespace LeanShared.UniformInverseCloseness

theorem exists_radius {X : Type*} [MetricSpace X] (T : X ≃ₜ X)
    (inverse : UniformContinuous T.symm) (error : ℝ) (positive : 0 < error) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f g : X → X,
      (∀ x, dist (f x) (T x) < δ) → Function.RightInverse g f →
      ∀ y, dist (g y) (T.symm y) < error := by
  obtain ⟨δ,positiveδ,bound⟩ := Metric.uniformContinuous_iff.mp inverse error positive
  refine ⟨δ,positiveδ,fun f g close right y => ?_⟩
  have near : dist (T (g y)) y < δ := by
    simpa only [right y,dist_comm] using close (g y)
  simpa only [Homeomorph.symm_apply_apply] using bound near

end LeanShared.UniformInverseCloseness
