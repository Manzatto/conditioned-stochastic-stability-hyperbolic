module
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Tactic.Linarith

/-! Uniform local injectivity becomes global for maps uniformly close to a
homeomorphism with uniformly continuous inverse. This is the topological
part of constructing actual inverse perturbations on a compact manifold. -/
public noncomputable section
namespace LeanShared.GlobalInjectivityNearHomeomorphism
open Set

theorem exists_radius
    {X : Type*} [MetricSpace X] (T : X ≃ₜ X)
    (inverse : UniformContinuous T.symm) (radius : ℝ) (positive : 0 < radius) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : X → X,
      (∀ x, dist (f x) (T x) < δ) →
      (∀ x y, dist x y < radius → f x = f y → x = y) →
      Function.Injective f := by
  obtain ⟨η,positiveη,control⟩ := Metric.uniformContinuous_iff.mp inverse radius positive
  refine ⟨η / 3,by positivity,fun f close locally x y equal => ?_⟩
  apply locally x y
  · have triangle := dist_triangle (T x) (f x) (T y)
    have left : dist (T x) (f x) < η / 3 := by simpa only [dist_comm] using close x
    have right : dist (f x) (T y) < η / 3 := equal.symm ▸ close y
    have near : dist (T x) (T y) < η := by linarith
    simpa only [Homeomorph.symm_apply_apply] using control near
  · exact equal

end LeanShared.GlobalInjectivityNearHomeomorphism
