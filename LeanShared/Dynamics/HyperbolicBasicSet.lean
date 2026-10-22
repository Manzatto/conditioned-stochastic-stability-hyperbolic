module

public import LeanShared.Dynamics.ReversibleTransitivity
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! Geometric hyperbolic-basic-set hypotheses on the actual tangent bundle.
Unlike a numerical cocycle certificate, the splitting has a continuous
projection on the restricted tangent bundle. The bounds use actual mfderiv
of forward and inverse iterates with the Riemannian fiber norms. -/

@[expose] public noncomputable section
open Set Function Bundle
open scoped Manifold ContDiff Topology Bundle
namespace LeanShared.HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

/-- Actual uniformly hyperbolic tangent data, with continuous splitting. -/
structure HyperbolicData (T : M ≃ₜ M) (Λ : Set M) where
  compact : IsCompact Λ
  invariant : T '' Λ = Λ
  stable : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x)
  unstable : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x)
  complementary : ∀ x ∈ Λ, IsCompl (stable x) (unstable x)
  projection : ∀ x : M,
    TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) x
  projection_range : ∀ x ∈ Λ, (projection x).range = stable x
  projection_kernel : ∀ x ∈ Λ, (projection x).ker = unstable x
  projection_idempotent : ∀ x ∈ Λ, (projection x).comp (projection x) = projection x
  continuous_splitting : ContinuousOn
    (fun v : TangentBundle (𝓘(ℝ, E)) M =>
      (⟨v.proj, projection v.proj v.2⟩ : TangentBundle (𝓘(ℝ, E)) M))
    {v | v.proj ∈ Λ}
  stable_invariant : ∀ x ∈ Λ,
    (stable x).map (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x).toLinearMap = stable (T x)
  unstable_invariant : ∀ x ∈ Λ,
    (unstable x).map (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) T x).toLinearMap = unstable (T x)
  constant : ℝ
  contraction : ℝ
  constant_pos : 0 < constant
  contraction_pos : 0 < contraction
  contraction_lt_one : contraction < 1
  stable_bound : ∀ n : ℕ, ∀ x ∈ Λ, ∀ v ∈ stable x,
    ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T : M → M)^[n]) x v‖ ≤
      constant * contraction ^ n * ‖v‖
  unstable_bound : ∀ n : ℕ, ∀ x ∈ Λ, ∀ v ∈ unstable x,
    ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T.symm : M → M)^[n]) x v‖ ≤
      constant * contraction ^ n * ‖v‖

/-- Both time directions of the actual homeomorphism orbit. -/
def orbit (T : M ≃ₜ M) (x : M) (n : ℤ) : M :=
  if 0 ≤ n then (T : M → M)^[n.toNat] x else (T.symm : M → M)^[(-n).toNat] x

/-- The paper's compact isolated transitive basic set, without a saddle-only
restriction or a mixing condition hidden in the definition. -/
structure BasicData (T : M ≃ₜ M) (Λ V : Set M) where
  hyperbolic : HyperbolicData (E := E) T Λ
  nonempty : Λ.Nonempty
  open_neighborhood : IsOpen V
  subset_neighborhood : Λ ⊆ V
  isolated : Λ = LeanShared.isolatedCore T (closure V)
  dense_orbit : ∃ x ∈ Λ, Λ ⊆ closure (range (orbit T x))

/-- Relative open-set topological mixing, with the eventual quantifier over
all sufficiently large integer times. -/
def MixingOn (T : M ≃ₜ M) (Λ : Set M) : Prop :=
  ∀ U W : Set M, IsOpen U → IsOpen W → (Λ ∩ U).Nonempty → (Λ ∩ W).Nonempty →
    ∃ N : ℕ, ∀ n ≥ N, ∃ x ∈ Λ ∩ U, (T : M → M)^[n] x ∈ W

omit [FiniteDimensional ℝ E] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] in
/-- Mixing supplies the transitivity used by the checked support producers. -/
theorem MixingOn.forwardTransitiveOn {T : M ≃ₜ M} {Λ : Set M} (h : MixingOn T Λ) :
    ControlledPlaqueClosure.forwardTransitiveOn T Λ := by
  apply (ReversibleTransitivity.forwardTransitiveOn_iff_hitting T Λ).mpr
  intro U W hU hW hΛU hΛW
  obtain ⟨N, hN⟩ := h U W hU hW hΛU hΛW
  exact ⟨N, hN N le_rfl⟩

end LeanShared.HyperbolicBasicSet
