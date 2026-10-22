module
public import LeanShared.Dynamics.BasicSetStableDimension
import Lean.Elab.Tactic.Omega

/-! The fixed stable and unstable dimensions of an actual differentiable basic
set are derived from its tangent splitting. The sum is exactly the dimension
of the manifold model. Zero-dimensional endpoints are retained. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff

set_option maxHeartbeats 2400000 in
theorem BasicData.exists_tangent_dimensions
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm) :
    ∃ ds du : ℕ, ds + du = Module.finrank ℝ E ∧
      ∀ x ∈ Λ, Module.finrank ℝ (b.hyperbolic.stable x) = ds ∧
        Module.finrank ℝ (b.hyperbolic.unstable x) = du := by
  have tangent_dimension (x : M) :
      Module.finrank ℝ (TangentSpace (𝓘(ℝ, E)) x) = Module.finrank ℝ E := by
    let e := trivializationAt E (TangentSpace (𝓘(ℝ, E))) x
    exact (e.continuousLinearEquivAt ℝ x (FiberBundle.mem_baseSet_trivializationAt' x)).toLinearEquiv.finrank_eq
  have sum (x : M) (hx : x ∈ Λ) :
      Module.finrank ℝ (b.hyperbolic.stable x) +
        Module.finrank ℝ (b.hyperbolic.unstable x) = Module.finrank ℝ E :=
    (Submodule.finrank_add_eq_of_isCompl (b.hyperbolic.complementary x hx)).trans (tangent_dimension x)
  obtain ⟨ds, stable⟩ := b.exists_stable_dimension forward inverse
  obtain ⟨x, hx⟩ := b.nonempty
  refine ⟨ds, Module.finrank ℝ (b.hyperbolic.unstable x), ?_, fun y hy => ⟨stable y hy, ?_⟩⟩
  · simpa only [stable x hx] using sum x hx
  · have source := sum x hx
    have target := sum y hy
    rw [stable x hx] at source
    rw [stable y hy] at target
    omega

end LeanShared.HyperbolicBasicSet
