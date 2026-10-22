module
public import LeanShared.Dynamics.HyperbolicBasicSet
public import LeanShared.Geometry.DiffeomorphismDifferential
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-! The actual diffeomorphism differential restricts to genuine continuous
linear equivalences between invariant stable/unstable tangent fibers. These
are constructed from the literal forward/inverse differentiability and the
actual invariant splitting, rather than supplied as an abstract cocycle. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff

set_option maxHeartbeats 1600000 in
theorem HyperbolicData.exists_stable_differential
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (x : M) (inside : x ∈ Λ) :
    ∃ A : h.stable x ≃L[ℝ] h.stable (T x),
      ∀ v, (A v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x v.val := by
  let D := DiffeomorphismDifferential.differential T forward inverse x
  have differential_eq : D.toLinearMap = (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x).toLinearMap := by
    ext v
    exact DiffeomorphismDifferential.differential_apply T forward inverse x v
  have mapped : (h.stable x).map D.toLinearMap = h.stable (T x) := by
    rw [differential_eq]
    exact h.stable_invariant x inside
  refine ⟨D.ofSubmodules (h.stable x) (h.stable (T x)) mapped, fun v => ?_⟩
  exact DiffeomorphismDifferential.differential_apply T forward inverse x v.val

set_option maxHeartbeats 1600000 in
theorem HyperbolicData.exists_unstable_differential
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (x : M) (inside : x ∈ Λ) :
    ∃ A : h.unstable x ≃L[ℝ] h.unstable (T x),
      ∀ v, (A v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x v.val := by
  let D := DiffeomorphismDifferential.differential T forward inverse x
  have differential_eq : D.toLinearMap = (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x).toLinearMap := by
    ext v
    exact DiffeomorphismDifferential.differential_apply T forward inverse x v
  have mapped : (h.unstable x).map D.toLinearMap = h.unstable (T x) := by
    rw [differential_eq]
    exact h.unstable_invariant x inside
  refine ⟨D.ofSubmodules (h.unstable x) (h.unstable (T x)) mapped, fun v => ?_⟩
  exact DiffeomorphismDifferential.differential_apply T forward inverse x v.val

end LeanShared.HyperbolicBasicSet
