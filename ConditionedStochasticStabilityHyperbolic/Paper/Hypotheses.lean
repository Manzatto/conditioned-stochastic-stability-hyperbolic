module

public import LeanShared.Dynamics.HyperbolicBasicSet
public import LeanShared.Geometry.FractionalManifoldRegularity

/-! The literal geometric hypothesis HL, before any anisotropic/spectral
source is supplied. Its regularity uses actual fractional chart derivatives;
hyperbolicity uses the actual tangent derivative and a continuous splitting.
No compact inclusion, transfer estimate, spectral pair or stochastic
conclusion is a field. Global hypothesis definitions are added separately
once their pressure and equilibrium-state semantics are in place. -/

@[expose] public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

/-- Manuscript HL, including the standing nonnegative-weight convention.
Saddle dimensions are deliberately not inserted into this hypothesis. -/
structure HL (T : M ≃ₜ M) (g : M → ℝ) (Λ V : Set M) where
  r : ℝ
  regularity_gt_one : 1 < r
  map_regular : FractionalManifoldRegularity.Regular (E := E) (F := E) r (T : M → M)
  inverse_regular : FractionalManifoldRegularity.Regular (E := E) (F := E) r (T.symm : M → M)
  basic : BasicData (E := E) T Λ V
  weight_regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (r - 1) g
  weight_nonnegative : ∀ x, 0 ≤ g x
  weight_supported : tsupport g ⊆ V
  weight_positive : ∀ x ∈ Λ, 0 < g x
  mixing : MixingOn T Λ

namespace HL
omit [FiniteDimensional ℝ E]
variable {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M} (h : HL (E := E) T g Λ V)
include h

/-- The actual HL mixing hypothesis supplies the transitivity consumed by the checked
forward/inverse support argument. -/
theorem transitive : ControlledPlaqueClosure.forwardTransitiveOn T Λ :=
  h.mixing.forwardTransitiveOn

theorem compact_core : IsCompact Λ := h.basic.hyperbolic.compact

theorem nonempty_core : Λ.Nonempty := h.basic.nonempty

theorem actual_isolated_core : Λ = LeanShared.isolatedCore T (closure V) := h.basic.isolated

end HL
end ConditionedStochasticStabilityHyperbolic.Paper
