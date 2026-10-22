module

public import LeanShared.Dynamics.BasicHyperbolicPeriodicPoints
public import LeanShared.Dynamics.BasicHyperbolicSmallScalePeriodicShadowing
public import Mathlib.Basic.ENNReal.BigOperators

/-! The actual full periodic-orbit partition sums bound, and are bounded by, literal separated partition sums. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff BigOperators ENNReal
open ThermodynamicDefinitions
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

@[expose] def BasicData.periodicPartitionSum (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (φ : M → ℝ) (p : ℕ) : ℝ :=
  if hp : 0 < p then
    ∑ x ∈ b.periodicPoints forward inverse p hp, Real.exp (orbitSum T φ p x)
  else 0

theorem BasicData.periodicPartitionSum_eq (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (φ : M → ℝ) (p : ℕ) (hp : 0 < p) :
    b.periodicPartitionSum forward inverse φ p =
      ∑ x ∈ b.periodicPoints forward inverse p hp, Real.exp (orbitSum T φ p x) := by
  simp only [periodicPartitionSum, dite_eq_left hp]

theorem BasicData.periodic_partition_upper (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm) :
    ∃ c > 0, ∀ (φ : M → ℝ) (p : ℕ), 0 < p →
      ENNReal.ofReal (b.periodicPartitionSum forward inverse φ p) ≤
        separatedPartitionSum T φ Λ p c := by
  obtain ⟨c, positiveC, separates⟩ := b.periodicPoints_separated forward inverse
  refine ⟨c, positiveC, fun φ p hp => ?_⟩
  rw [b.periodicPartitionSum_eq forward inverse φ p hp,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  unfold separatedPartitionSum
  exact le_iSup_of_le (b.periodicPoints forward inverse p hp) (le_iSup_of_le (separates p hp) le_rfl)

set_option maxHeartbeats 2000000 in
theorem BasicData.periodic_partition_lower (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (mixing : MixingOn T Λ) (ψ : M → ℝ) (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ)
    (ρ : ℝ) (positiveρ : 0 < ρ) :
    ∃ ε > 0, ε ≤ ρ ∧ ∃ gap : ℕ, 0 < gap ∧ ∃ a > 0, ∀ n : ℕ,
      ENNReal.ofReal a * separatedPartitionSum T ψ Λ (n + 1) (3 * ε) ≤
        ENNReal.ofReal (b.periodicPartitionSum forward inverse ψ (n + gap)) := by
  obtain ⟨ε, positiveε, smallε, gap, positiveGap, a, positiveA, closes⟩ :=
    b.small_scale_weighted_periodic_shadowing forward inverse mixing ψ α positiveα smallα regular ρ positiveρ
  refine ⟨ε, positiveε, smallε, gap, positiveGap, a, positiveA, fun n => ?_⟩
  unfold separatedPartitionSum
  simp only [ENNReal.mul_iSup]
  refine iSup_le fun s => iSup_le fun separated => ?_
  obtain ⟨q, member, fixed, comparison⟩ := closes n s separated
  have subset : q ⊆ b.periodicPoints forward inverse (n + gap) (by omega) := by
    intro z hz
    exact (b.mem_periodicPoints forward inverse (n + gap) (by omega) z).mpr
      ⟨member.1 z hz, fixed z hz⟩
  have fullSum := Finset.sum_le_sum_of_subset_of_nonneg subset
    (fun x _ _ => (Real.exp_pos (orbitSum T ψ (n + gap) x)).le)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le),
    ← ENNReal.ofReal_mul positiveA.le]
  apply ENNReal.ofReal_le_ofReal
  rw [b.periodicPartitionSum_eq forward inverse ψ (n + gap) (by omega)]
  exact comparison.trans fullSum

end LeanShared.HyperbolicBasicSet
