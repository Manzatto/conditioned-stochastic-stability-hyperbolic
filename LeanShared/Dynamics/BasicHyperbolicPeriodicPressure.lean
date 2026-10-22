module

public import LeanShared.Dynamics.BasicHyperbolicPeriodicExponentialLower
public import LeanShared.Dynamics.BasicHyperbolicPartitionExponentialUpper
public import LeanShared.Analysis.ExponentialGrowthLogLimit

/-! The actual full periodic-orbit partition sums compute the literal pressure of an actual mixing hyperbolic basic set and fractional potential. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open Filter
open scoped Topology Manifold ContDiff BigOperators ENNReal
open ThermodynamicDefinitions
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

set_option maxHeartbeats 2400000 in
theorem BasicData.periodic_pressure_limit (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (mixing : MixingOn T Λ) (ψ : M → ℝ) (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ) :
    ∃ P : ℝ, pressure T ψ Λ = (P : EReal) ∧
      Tendsto (fun n : ℕ => Real.log (b.periodicPartitionSum forward inverse ψ n) / (n : ℝ))
        atTop (𝓝 P) := by
  obtain ⟨P, pressureP, gap, _, C, positiveC, lower⟩ :=
    b.periodic_partition_exponential_lower forward inverse mixing ψ α positiveα smallα regular
  obtain ⟨Q, pressureQ, upper⟩ := b.eventual_partition_exponential_upper forward inverse ψ
    regular.differentiable.continuous
  have same : P = Q := EReal.coe_injective (pressureP.symm.trans pressureQ)
  subst Q
  obtain ⟨c, positiveC', periodicUpper⟩ := b.periodic_partition_upper forward inverse
  refine ⟨P, pressureP, ExponentialGrowthLogLimit.tendsto
    (b.periodicPartitionSum forward inverse ψ) P C positiveC gap lower ?_⟩
  intro η positiveη
  filter_upwards [upper c positiveC' η positiveη] with n bound
  have comparison := (periodicUpper ψ (n + 1) (by omega)).trans bound
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp comparison

end LeanShared.HyperbolicBasicSet
