module
public import LeanShared.Dynamics.BasicHyperbolicStrictNativeCostPartition
public import LeanShared.Analysis.FiniteStrictCostBudget

/-! The actual strict pressure partition has one positive additive budget
per fixed center and label. All later finite collar/noise perturbations
within this margin preserve the same strict principal block. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle ThermodynamicDefinitions FiniteSmoothCapturePartition PressureCoverRefinement
open scoped Manifold ContDiff BigOperators Topology
attribute [local instance] Classical.propDecidable
variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype I]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {v : I → Set M}

theorem BasicData.exists_strict_native_cost_margin (b : BasicData (E := E) T Λ V)
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
    ∃ p : FiniteSmoothCapturePartition.Data (E := E) Λ
      (fun y : centers => BowenOpenCoverCoefficient.orbitBall T (N+1) radius y.val),
      Λ ⊆ p.capture ∧
      (∀ y : centers, IsCompact (Λ ∩ tsupport (p.beta y))) ∧
      (∀ y : centers, Λ ∩ tsupport (p.beta y) ⊆
        BowenOpenCoverCoefficient.orbitBall T (N+1) radius y.val) ∧
      (Λ ⊆ ⋃ y : centers, Λ ∩ tsupport (p.beta y)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ cost : centers → (Fin (N+1) → I) → ℝ,
        (∀ y labels, cost y labels ≤
          domainCoefficient Λ (BowenOpenCoverCoefficient.orbitBall T (N+1) radius y.val)
            (b.hyperbolic.localizedNativeCost d g N labels) + δ) →
        A * max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s) *
          (∑ y : centers, ∑ labels : Fin (N+1) → I, cost y labels) < ρ^N := by
  obtain ⟨P,pressureP,ρ,radius,positiveρ,belowPressure,positiveRadius,N,positiveN,aboveMinimum,
    centers,p,captureP,compactPieces,insidePieces,coverPieces,strict⟩ :=
      b.exists_strict_native_cost_partition forward inverse g continuous positive d capture
        positiveμ smallμ largeν positiveT negativeS A nonnegativeA minimum
  let q : centers × (Fin (N+1) → I) → ℝ := fun i =>
    domainCoefficient Λ (BowenOpenCoverCoefficient.orbitBall T (N+1) radius i.1.val)
      (b.hyperbolic.localizedNativeCost d g N i.2)
  let factor := A * max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s)
  have nonnegativeFactor : 0 ≤ factor :=
    mul_nonneg nonnegativeA ((Real.rpow_nonneg (by positivity) t).trans (le_max_left _ _))
  have strictQ : factor * ∑ i, q i < ρ^N := by
    simp only [q,factor,Fintype.sum_prod_type]
    rw [Finset.sum_coe_sort centers (fun x => ∑ labels : Fin (N+1) → I,
      domainCoefficient Λ (BowenOpenCoverCoefficient.orbitBall T (N+1) radius x)
        (b.hyperbolic.localizedNativeCost d g N labels))]
    exact strict
  obtain ⟨δ,positiveδ,budget⟩ := FiniteStrictCostBudget.exists_margin q factor (ρ^N) nonnegativeFactor strictQ
  refine ⟨P,pressureP,ρ,radius,positiveρ,belowPressure,positiveRadius,N,positiveN,aboveMinimum,
    centers,p,captureP,compactPieces,insidePieces,coverPieces,δ,positiveδ,?_⟩
  intro cost bound
  have result := budget (fun i => cost i.1 i.2) (fun i => bound i.1 i.2)
  simpa only [factor,Fintype.sum_prod_type] using result

end LeanShared.HyperbolicBasicSet
