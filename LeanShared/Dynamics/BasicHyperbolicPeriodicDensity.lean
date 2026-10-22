module

public import LeanShared.Dynamics.BasicHyperbolicPeriodicSpecification
public import Mathlib.Dynamics.PeriodicPts.Defs

/-! Mixing basic hyperbolic data have dense genuine periodic points in
their literal core. The periodic approximants, including their positive
periods, are constructed by the proved periodic-specification theorem. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle Function
open scoped Topology Manifold ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

/-- Every core point admits a nearby periodic point in the same core. -/
theorem BasicData.exists_periodic_near (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (mixing : MixingOn T Λ) (x : M) (hx : x ∈ Λ)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ z ∈ Λ ∩ periodicPts (T : M → M), dist z x < ε := by
  obtain ⟨gap, positiveGap, shadows⟩ :=
    b.periodic_specification forward inverse mixing ε positiveε
  obtain ⟨z, member, fixed, near⟩ := shadows 0 x hx
  refine ⟨z, ⟨member, ?_⟩, ?_⟩
  · exact ⟨gap, positiveGap, by simpa only [IsPeriodicPt, IsFixedPt, zero_add] using fixed⟩
  · simpa only [Function.iterate_zero_apply] using near 0 le_rfl

/-- Periodic density is obtained inside the actual core, rather than only
in the ambient nonwandering set. -/
theorem BasicData.periodic_dense_on_core (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (mixing : MixingOn T Λ) :
    Λ ⊆ closure (Λ ∩ periodicPts (T : M → M)) := by
  intro x hx
  apply mem_closure_iff.mpr
  intro U openU memberU
  obtain ⟨ε, positiveε, contained⟩ := Metric.isOpen_iff.mp openU x memberU
  obtain ⟨z, member, near⟩ := b.exists_periodic_near forward inverse mixing x hx ε positiveε
  exact ⟨z, contained (by simpa only [Metric.mem_ball] using near), member⟩

/-- Compactness of the core gives the reverse closure inclusion. -/
theorem BasicData.closure_periodic_inter_core (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (mixing : MixingOn T Λ) :
    closure (Λ ∩ periodicPts (T : M → M)) = Λ := by
  exact Subset.antisymm
    (closure_minimal inter_subset_left b.hyperbolic.compact.isClosed)
    (b.periodic_dense_on_core forward inverse mixing)

/-- Full-manifold mixing basic data produce the periodic-density field
required by the independent auxiliary Anosov construction. -/
theorem BasicData.closure_periodic_eq_univ
    (b : BasicData (E := E) T univ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (mixing : MixingOn T univ) :
    closure (periodicPts (T : M → M)) = univ := by
  simpa only [univ_inter] using b.closure_periodic_inter_core forward inverse mixing

end LeanShared.HyperbolicBasicSet
