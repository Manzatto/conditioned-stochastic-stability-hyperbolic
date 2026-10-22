module
public import LeanShared.Dynamics.BasicHyperbolicNativeCostCover
public import LeanShared.Analysis.AdaptedPrincipalPressureBudget

/-! An actual finite endpoint-aware core cover, with all literal localized
native-Jacobian costs, has a strict adapted principal block. The block may
exceed any prescribed threshold. No pressure or cover oracle is supplied. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle ThermodynamicDefinitions FiniteSmoothCapturePartition PressureCoverRefinement Filter
open scoped Manifold ContDiff BigOperators Topology
attribute [local instance] Classical.propDecidable
variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype I]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {v : I → Set M}

theorem BasicData.exists_strict_native_cost_cover (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (g : M → ℝ) (continuous : ContinuousOn g Λ) (positive : ∀ x ∈ Λ, 0 < g x)
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ v) (capture : Λ ⊆ d.capture)
    {μ ν t s : ℝ} (positiveμ : 0 < μ) (smallμ : μ < 1) (largeν : 1 < ν)
    (positiveT : 0 < t) (negativeS : s < 0) (A : ℝ) (nonnegativeA : 0 ≤ A)
    (minimum : ℕ) :
    ∃ P : ℝ, pressure T (b.hyperbolic.potential g) Λ = (P : EReal) ∧
    ∃ ρ radius : ℝ, 0 < ρ ∧ ρ < Real.exp P ∧ 0 < radius ∧
    ∃ N : ℕ, 0 < N ∧ minimum ≤ N ∧ ∃ centers : Finset M,
      Separated T Λ (N+1) radius centers ∧
      (∀ x, IsOpen (BowenOpenCoverCoefficient.orbitBall T (N+1) radius x)) ∧
      (Λ ⊆ ⋃ x ∈ centers, BowenOpenCoverCoefficient.orbitBall T (N+1) radius x) ∧
      A * max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s) *
        (∑ x ∈ centers, ∑ labels : Fin (N+1) → I,
          domainCoefficient Λ (BowenOpenCoverCoefficient.orbitBall T (N+1) radius x)
            (b.hyperbolic.localizedNativeCost d g N labels)) < ρ^N := by
  obtain ⟨P,pressureP,growth⟩ := b.eventual_native_cost_open_cover forward inverse g continuous positive d capture
  obtain ⟨ε,ρ,positiveε,positiveρ,belowPressure,budget⟩ :=
    AdaptedPrincipalPressureBudget.exists_budget positiveμ smallμ largeν positiveT negativeS A P nonnegativeA
  obtain ⟨radius,D,positiveRadius,positiveD,covers⟩ := growth ε positiveε
  obtain ⟨threshold,beyond⟩ := eventually_atTop.mp (covers.and (budget D positiveD))
  let N := max threshold minimum + 1
  have aboveThreshold : threshold ≤ N := (Nat.le_max_left _ _).trans (Nat.le_succ _)
  have aboveMinimum : minimum ≤ N := (Nat.le_max_right _ _).trans (Nat.le_succ _)
  obtain ⟨⟨centers,separated,openBalls,cover,costBound⟩,strictBound⟩ := beyond N aboveThreshold
  refine ⟨P,pressureP,ρ,radius,positiveρ,belowPressure,positiveRadius,N,Nat.succ_pos _,
    aboveMinimum,centers,separated,openBalls,cover,?_⟩
  have factorNonnegative : 0 ≤ A * max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s) :=
    mul_nonneg nonnegativeA ((Real.rpow_nonneg (by positivity) t).trans (le_max_left _ _))
  exact (mul_le_mul_of_nonneg_left costBound factorNonnegative).trans_lt strictBound

end LeanShared.HyperbolicBasicSet
