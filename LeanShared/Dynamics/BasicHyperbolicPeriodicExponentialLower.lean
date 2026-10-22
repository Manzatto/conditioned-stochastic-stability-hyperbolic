module

public import LeanShared.Dynamics.BasicHyperbolicPeriodicPartition
public import LeanShared.Dynamics.BasicHyperbolicTwoSidedPartition

/-! Full periodic-orbit sums have the actual pressure as an exponential lower growth rate; all closing and partition normalization are derived. -/
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

set_option maxHeartbeats 2400000 in
theorem BasicData.periodic_partition_exponential_lower (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (mixing : MixingOn T Λ) (ψ : M → ℝ) (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ) :
    ∃ P : ℝ, pressure T ψ Λ = (P : EReal) ∧ ∃ gap : ℕ, 0 < gap ∧ ∃ C > 0,
      ∀ n : ℕ, C * Real.exp (((n + 1 : ℕ) : ℝ) * P) ≤
        b.periodicPartitionSum forward inverse ψ (n + gap) := by
  obtain ⟨ρ, positiveρ, P, pressureP, A, positiveA, _, _, normalization⟩ :=
    b.two_sided_partition_normalization forward inverse mixing ψ α positiveα smallα regular
  obtain ⟨ε, _, smallε, gap, positiveGap, a, positiveA', comparison⟩ :=
    b.periodic_partition_lower forward inverse mixing ψ α positiveα smallα regular
      (ρ / 3) (by positivity)
  refine ⟨P, pressureP, gap, positiveGap, a * A, mul_pos positiveA' positiveA, fun n => ?_⟩
  have scale : separatedPartitionSum T ψ Λ (n + 1) ρ ≤
      separatedPartitionSum T ψ Λ (n + 1) (3 * ε) := by
    unfold separatedPartitionSum
    refine iSup_le fun s => iSup_le fun separated => ?_
    have fine : Separated T Λ (n + 1) (3 * ε) s := by
      refine ⟨separated.1, fun x hx y hy different => ?_⟩
      obtain ⟨j, hj, apart⟩ := separated.2 x hx y hy different
      exact ⟨j, hj, (by linarith : 3 * ε ≤ ρ).trans apart⟩
    exact le_iSup_of_le s (le_iSup_of_le fine le_rfl)
  have lower : ENNReal.ofReal (A * Real.exp (((n + 1 : ℕ) : ℝ) * P)) ≤
      separatedPartitionSum T ψ Λ (n + 1) ρ :=
    (ENNReal.ofReal_le_ofReal ((normalization (n + 1) (by omega)).1)).trans ENNReal.ofReal_toReal_le
  have bound := (mul_le_mul' (le_refl (ENNReal.ofReal a)) (lower.trans scale)).trans (comparison n)
  rw [← ENNReal.ofReal_mul positiveA'.le] at bound
  have nonnegative : 0 ≤ b.periodicPartitionSum forward inverse ψ (n + gap) := by
    rw [b.periodicPartitionSum_eq forward inverse ψ (n + gap) (by omega)]
    exact Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  have realBound := (ENNReal.ofReal_le_ofReal_iff nonnegative).mp bound
  simpa only [mul_assoc] using realBound

end LeanShared.HyperbolicBasicSet
