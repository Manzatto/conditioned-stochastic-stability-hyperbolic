module
public import LeanShared.Dynamics.HyperbolicEuclideanBlocks
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The actual complementary invariant tangent splitting produces a whole coordinate map. In these
coordinates the actual iterated derivative is exactly block diagonal, with the derived
contraction bounds. The unstable coordinate comes first, as in the backward graph transform. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

private def splitFrame
    {P Q H : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (u s : Submodule ℝ H) (complementary : IsCompl u s)
    (eu : P ≃ₗᵢ[ℝ] u) (es : Q ≃ₗᵢ[ℝ] s) : (P × Q) ≃L[ℝ] H :=
  ((eu.toLinearEquiv.prodCongr es.toLinearEquiv).trans
    (u.prodEquivOfIsCompl s complementary)).toContinuousLinearEquiv

private theorem splitFrame_apply
    {P Q H : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (u s : Submodule ℝ H) (complementary : IsCompl u s)
    (eu : P ≃ₗᵢ[ℝ] u) (es : Q ≃ₗᵢ[ℝ] s) (z : P × Q) :
    splitFrame u s complementary eu es z = (eu z.1).val + (es z.2).val := rfl

set_option maxHeartbeats 2400000 in
theorem BasicData.exists_actual_split_coordinates
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (κ : ℝ) (positive : 0 < κ) :
    ∃ ds du N : ℕ, ds + du = Module.finrank ℝ E ∧ 0 < N ∧
      ∀ x ∈ Λ,
        ∃ e : (EuclideanSpace ℝ (Fin du) × EuclideanSpace ℝ (Fin ds)) ≃L[ℝ]
          TangentSpace (𝓘(ℝ, E)) x,
        ∃ f : (EuclideanSpace ℝ (Fin du) × EuclideanSpace ℝ (Fin ds)) ≃L[ℝ]
          TangentSpace (𝓘(ℝ, E)) ((T^N) x),
        ∃ S : EuclideanSpace ℝ (Fin ds) ≃L[ℝ] EuclideanSpace ℝ (Fin ds),
        ∃ U : EuclideanSpace ℝ (Fin du) ≃L[ℝ] EuclideanSpace ℝ (Fin du),
          ‖S.toContinuousLinearMap‖ ≤ κ ∧ ‖U.symm.toContinuousLinearMap‖ ≤ κ ∧
          ∀ z, f.symm (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
            ((T^N : M ≃ₜ M) : M → M) x (e z)) = (U z.1, S z.2) := by
  obtain ⟨ds, du, N, dimension, positiveN, blocks⟩ :=
    b.exists_actual_euclidean_blocks forward inverse κ positive
  refine ⟨ds, du, N, dimension, positiveN, fun x hx => ?_⟩
  have preserves : MapsTo T Λ Λ := fun y hy => by
    rw [← b.hyperbolic.invariant]
    exact mem_image_of_mem T hy
  have target : (T^N) x ∈ Λ := by
    rw [DiffeomorphismIterates.coe_pow]
    exact preserves.iterate N hx
  obtain ⟨es, fs, eu, fu, S, U, boundS, boundU, actionS, actionU, _⟩ := blocks x hx
  let e := splitFrame _ _ (b.hyperbolic.complementary x hx).symm eu es
  let f := splitFrame _ _ (b.hyperbolic.complementary ((T^N) x) target).symm fu fs
  refine ⟨e, f, S, U, boundS, boundU, fun z => ?_⟩
  apply f.injective
  rw [f.apply_symm_apply]
  change mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^N : M ≃ₜ M) : M → M) x
    (splitFrame _ _ _ eu es z) = splitFrame _ _ _ fu fs (U z.1, S z.2)
  rw [splitFrame_apply, splitFrame_apply, map_add]
  exact congrArg₂ (fun a b => a + b) (actionU z.1).symm (actionS z.2).symm

end LeanShared.HyperbolicBasicSet
