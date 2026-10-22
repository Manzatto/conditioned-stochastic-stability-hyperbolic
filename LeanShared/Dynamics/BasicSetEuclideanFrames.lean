module
public import LeanShared.Dynamics.BasicSetDimensions
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Fixed Euclidean parameter spaces for every actual stable/unstable tangent
fiber of a basic set. The dimensions and isometric frames are constructed;
zero-dimensional endpoints are allowed. No global continuous trivialization
is asserted (local projection frames handle continuity separately). -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

private def euclideanFrame {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (n : ℕ) (dimension : Module.finrank ℝ H = n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] H :=
  ((stdOrthonormalBasis ℝ H).reindex (Fin.castOrderIso dimension).toEquiv).repr.symm

set_option maxHeartbeats 2400000 in
theorem BasicData.exists_euclidean_tangent_frames
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm) :
    ∃ ds du : ℕ, ds + du = Module.finrank ℝ E ∧
      ∀ x ∈ Λ, Nonempty (EuclideanSpace ℝ (Fin ds) ≃ₗᵢ[ℝ] b.hyperbolic.stable x) ∧
        Nonempty (EuclideanSpace ℝ (Fin du) ≃ₗᵢ[ℝ] b.hyperbolic.unstable x) := by
  obtain ⟨ds, du, sum, dimensions⟩ := b.exists_tangent_dimensions forward inverse
  refine ⟨ds, du, sum, fun x hx => ⟨?_, ?_⟩⟩
  · exact ⟨euclideanFrame ds (dimensions x hx).1⟩
  · exact ⟨euclideanFrame du (dimensions x hx).2⟩

end LeanShared.HyperbolicBasicSet
