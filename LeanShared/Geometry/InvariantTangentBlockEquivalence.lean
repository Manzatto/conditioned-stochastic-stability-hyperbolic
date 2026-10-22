module
public import LeanShared.Geometry.InvariantTangentDistributionIterates
public import LeanShared.Geometry.DiffeomorphismIterates
public import LeanShared.Geometry.DiffeomorphismInverseDifferential
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-! The actual differential of an iterated diffeomorphism restricts to a
continuous linear equivalence on an invariant tangent distribution. Both its
forward and inverse actions are identified with actual manifold derivatives;
no independent block-cocycle or inverse-comparison data are required. -/
public noncomputable section
namespace LeanShared.InvariantTangentDistributionIterates
open Set IsManifold
open scoped Manifold

set_option maxHeartbeats 1600000 in
theorem exists_block_equivalence
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (T : M ≃ₜ M)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (K : Set M) (preserves : MapsTo T K K)
    (S : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x))
    (invariant : ∀ x ∈ K,
      (S x).map (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x).toLinearMap = S (T x))
    (n : ℕ) (x : M) (inside : x ∈ K) :
    ∃ A : S x ≃L[ℝ] S ((T^n) x),
      (∀ v, (A v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^n : M ≃ₜ M) : M → M) x v.val) ∧
      (∀ v, (A.symm v).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
        ((T^n).symm : M → M) ((T^n) x) v.val) := by
  let forwardN := DiffeomorphismIterates.mdifferentiable_pow T forward n
  let inverseN := DiffeomorphismIterates.mdifferentiable_symm_pow T inverse n
  let D := DiffeomorphismDifferential.differential (T^n) forwardN inverseN x
  have differential_eq : D.toLinearMap =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^n : M ≃ₜ M) : M → M) x).toLinearMap := by
    ext v
    exact DiffeomorphismDifferential.differential_apply (T^n) forwardN inverseN x v
  have mapped : (S x).map D.toLinearMap = S ((T^n) x) := by
    have iterated := map_iterate T forward K preserves S invariant n x inside
    rw [← DiffeomorphismIterates.coe_pow T n] at iterated
    rw [differential_eq]
    exact iterated
  refine ⟨D.ofSubmodules (S x) (S ((T^n) x)) mapped, ?_, ?_⟩
  · intro v
    exact DiffeomorphismDifferential.differential_apply (T^n) forwardN inverseN x v.val
  · intro v
    exact DiffeomorphismDifferential.differential_symm_apply (T^n) forwardN inverseN x v.val

end LeanShared.InvariantTangentDistributionIterates
