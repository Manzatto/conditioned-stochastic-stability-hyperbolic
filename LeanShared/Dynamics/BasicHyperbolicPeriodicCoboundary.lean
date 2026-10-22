module

public import LeanShared.Dynamics.BasicHyperbolicPeriodicPartition
public import LeanShared.Dynamics.PressureCoboundary

/-! Full periodic partition sums are exactly invariant under an actual
core coboundary, with no metric regularity of the coboundary. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle ThermodynamicDefinitions
open scoped Topology Manifold ContDiff BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

theorem BasicData.periodic_partition_coboundary (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (φ ψ u : M → ℝ) (same : ∀ x ∈ Λ, φ x = ψ x + u x - u (T x)) (p : ℕ) :
    b.periodicPartitionSum forward inverse φ p = b.periodicPartitionSum forward inverse ψ p := by
  classical
  have invariant : MapsTo (T : M → M) Λ Λ := image_subset_iff.mp b.hyperbolic.invariant.subset
  by_cases positiveP : 0 < p
  · rw [b.periodicPartitionSum_eq forward inverse φ p positiveP,
      b.periodicPartitionSum_eq forward inverse ψ p positiveP]
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨inside, fixed⟩ := (b.mem_periodicPoints forward inverse p positiveP x).mp hx
    have energy := orbitSum_coboundary invariant same p inside
    rw [fixed, add_sub_cancel_right] at energy
    rw [energy]
  · simp only [periodicPartitionSum, dite_eq_right positiveP]

end LeanShared.HyperbolicBasicSet
