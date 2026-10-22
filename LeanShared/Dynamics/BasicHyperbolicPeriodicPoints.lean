module

public import LeanShared.Dynamics.HyperbolicExpansivity
public import LeanShared.Dynamics.ExpansivePeriodicFiniteness

/-! The complete positive-period point sets of literal hyperbolic basic
data are finite and uniformly Bowen-separated. No periodic-point or
finite-trace source is assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

theorem BasicData.periodic_points_finite (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (p : ℕ) (positiveP : 0 < p) :
    {x : M | x ∈ Λ ∧ (T : M → M)^[p] x = x}.Finite := by
  obtain ⟨c, positiveC, expansive⟩ := b.exists_expansivity_radius forward inverse
  exact ExpansivePeriodicSeparation.finite T Λ b.hyperbolic.compact
    (image_subset_iff.mp b.hyperbolic.invariant.subset) c positiveC expansive p positiveP

@[expose] def BasicData.periodicPoints (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (p : ℕ) (positiveP : 0 < p) : Finset M :=
  (b.periodic_points_finite forward inverse p positiveP).toFinset

theorem BasicData.mem_periodicPoints (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (p : ℕ) (positiveP : 0 < p) (x : M) :
    x ∈ b.periodicPoints forward inverse p positiveP ↔ x ∈ Λ ∧ (T : M → M)^[p] x = x := by
  exact Set.Finite.mem_toFinset _

theorem BasicData.periodicPoints_separated (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm) :
    ∃ c > 0, ∀ p : ℕ, ∀ positiveP : 0 < p,
      ThermodynamicDefinitions.Separated T Λ p c (b.periodicPoints forward inverse p positiveP) := by
  obtain ⟨c, positiveC, expansive⟩ := b.exists_expansivity_radius forward inverse
  refine ⟨c, positiveC, fun p positiveP => ?_⟩
  apply ExpansivePeriodicSeparation.separated T Λ c expansive p positiveP
  · intro x hx
    exact ((b.mem_periodicPoints forward inverse p positiveP x).mp hx).1
  · intro x hx
    exact ((b.mem_periodicPoints forward inverse p positiveP x).mp hx).2

end LeanShared.HyperbolicBasicSet
