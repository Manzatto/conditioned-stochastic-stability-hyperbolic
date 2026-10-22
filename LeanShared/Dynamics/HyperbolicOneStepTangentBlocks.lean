module
public import LeanShared.Dynamics.HyperbolicBasicSet
public import LeanShared.Geometry.DiffeomorphismInverseDifferential
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-! Literal one-step restrictions of the actual diffeomorphism differential
to both invariant tangent subspaces, with the actual inverse differential. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

theorem HyperbolicData.actual_one_step_tangent_blocks
    (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (backward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (x : M) (inside : x ∈ Λ) :
    ∃ S : h.stable x ≃L[ℝ] h.stable (T x),
    ∃ U : h.unstable x ≃L[ℝ] h.unstable (T x),
      (∀ v, (S v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x v.val) ∧
      (∀ v, (U v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x v.val) ∧
      (∀ v, (U.symm v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm (T x) v.val) := by
  let D := DiffeomorphismDifferential.differential T forward backward x
  have differential : D.toLinearMap = (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x).toLinearMap := by
    ext v
    exact DiffeomorphismDifferential.differential_apply T forward backward x v
  have stableMap : (h.stable x).map D.toLinearMap = h.stable (T x) := by
    rw [differential]
    exact h.stable_invariant x inside
  have unstableMap : (h.unstable x).map D.toLinearMap = h.unstable (T x) := by
    rw [differential]
    exact h.unstable_invariant x inside
  refine ⟨D.ofSubmodules (h.stable x) (h.stable (T x)) stableMap,
    D.ofSubmodules (h.unstable x) (h.unstable (T x)) unstableMap, ?_, ?_, ?_⟩
  · intro v
    exact DiffeomorphismDifferential.differential_apply T forward backward x v.val
  · intro v
    exact DiffeomorphismDifferential.differential_apply T forward backward x v.val
  · intro v
    exact DiffeomorphismDifferential.differential_symm_apply T forward backward x v.val

end LeanShared.HyperbolicBasicSet
