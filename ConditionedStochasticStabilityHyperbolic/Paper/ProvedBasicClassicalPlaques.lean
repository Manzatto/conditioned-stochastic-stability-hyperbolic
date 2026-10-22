module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedClassicalPlaqueGeometry

/-! Literal basic-set data construct their coherent chart family and tangent
frames internally. No adapted chart, random plaque or capture packet is an
input to this forward random-manifold theorem. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle NNReal
open LeanShared.HyperbolicBasicSet

set_option maxHeartbeats 3200000 in
theorem Maps.eventually_basic_classical_plaques
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {r : ℝ} {Λ V₀ V K G : Set M}
    (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (basic : BasicData (E := E) T Λ V₀)
    (compactK : IsCompact K) (core : LeanShared.isolatedCore T K ⊆ Λ)
    (openV : IsOpen V) (insideK : V ⊆ K) (containsV : Λ ⊆ V)
    (openG : IsOpen G) (containsG : Λ ⊆ G) :
    ∃ window : ℝ≥0, 0 < window ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ window →
      Nonempty (ClassicalPlaqueGeometry (fun p : M × FixedControl (ι := ι) => F.fixedMap ε p.1 p.2) V K G) := by
  obtain ⟨geometry⟩ := basic.hyperbolic.exists_pseudo_reference_geometry (deterministic.mdifferentiable (by norm_num)) inverse
  obtain ⟨a⟩ := basic.exists_isometricFraming (deterministic.mdifferentiable (by norm_num)) inverse
  exact F.eventually_classical_plaque_geometry regularity deterministic geometry a compactK core
    basic.hyperbolic.compact (fun x hx => basic.hyperbolic.invariant ▸ mem_image_of_mem T hx)
    openV insideK containsV openG containsG

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
