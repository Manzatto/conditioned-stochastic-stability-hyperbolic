module

public import LeanShared.Dynamics.BasicHyperbolicPeriodicSpecification
public import LeanShared.Dynamics.BasicHyperbolicPeriodicPartition

/-! A literal mixing basic set has points of every sufficiently large
period. Hence its actual full periodic partition sums are eventually
strictly positive, including for arbitrary scalar potentials. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle Filter
open scoped Topology Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

theorem BasicData.eventually_periodic_points (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm) (mixing : MixingOn T Λ) :
    ∀ᶠ p : ℕ in atTop, ∃ z ∈ Λ, (T : M → M)^[p] z = z := by
  obtain ⟨gap, _, shadows⟩ := b.periodic_specification forward inverse mixing 1 zero_lt_one
  obtain ⟨x, hx⟩ := b.nonempty
  filter_upwards [eventually_ge_atTop gap] with p hp
  obtain ⟨z, hz, fixed, _⟩ := shadows (p - gap) x hx
  rw [Nat.sub_add_cancel hp] at fixed
  exact ⟨z, hz, fixed⟩

theorem BasicData.eventually_periodic_partition_positive (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm) (mixing : MixingOn T Λ)
    (φ : M → ℝ) :
    ∀ᶠ p : ℕ in atTop, 0 < b.periodicPartitionSum forward inverse φ p := by
  filter_upwards [b.eventually_periodic_points forward inverse mixing, eventually_gt_atTop 0]
    with p periodic positiveP
  obtain ⟨x, hx, fixed⟩ := periodic
  rw [b.periodicPartitionSum_eq forward inverse φ p positiveP]
  apply Finset.sum_pos (fun _ _ => Real.exp_pos _)
  exact ⟨x, (b.mem_periodicPoints forward inverse p positiveP x).mpr ⟨hx, fixed⟩⟩

end LeanShared.HyperbolicBasicSet
