module

public import ConditionedStochasticStabilityHyperbolic.Paper.Hypotheses
public import ConditionedStochasticStabilityHyperbolic.Paper.BasicAnalyticData
public import LeanShared.Dynamics.ProvedHyperbolicEquilibriumPackage

/-! Literal HL constructs its actual pressure/equilibrium package.
No thermodynamic, unstable-potential regularity, reference metric, Gibbs
measure or uniqueness source remains. A nonmixing BasicAnalyticData value
can use the same result precisely when actual mixing is available. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet Bundle
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M}

theorem BasicAnalyticData.exists_proved_equilibriumPackage (h : BasicAnalyticData (E := E) T g Λ V)
    (mixing : MixingOn T Λ) : Nonempty (EquilibriumPackage h.basic.hyperbolic g) :=
  h.basic.exists_proved_equilibriumPackage h.regularity_gt_one (by linarith [h.regularity_gt_one])
    h.map_regular h.inverse_regular mixing g h.weight_regular h.weight_positive

theorem HL.exists_proved_equilibriumPackage (h : HL (E := E) T g Λ V) :
    Nonempty (EquilibriumPackage h.basic.hyperbolic g) :=
  h.basic.exists_proved_equilibriumPackage h.regularity_gt_one (by linarith [h.regularity_gt_one])
    h.map_regular h.inverse_regular h.mixing g h.weight_regular h.weight_positive

@[expose] def HL.proved_equilibriumPackage (h : HL (E := E) T g Λ V) :
    EquilibriumPackage h.basic.hyperbolic g := Classical.choice h.exists_proved_equilibriumPackage

end ConditionedStochasticStabilityHyperbolic.Paper
