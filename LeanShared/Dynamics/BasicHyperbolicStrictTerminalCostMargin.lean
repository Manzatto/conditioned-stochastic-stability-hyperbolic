module
public import LeanShared.Dynamics.BasicHyperbolicStrictNativeCostMargin

/-! Independent terminal input slots cost only a fixed finite factor.
That factor is included before selecting the strict pressure block length;
no terminal partition factor is removed from the native cost. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle ThermodynamicDefinitions FiniteSmoothCapturePartition PressureCoverRefinement
open scoped Manifold ContDiff BigOperators Topology
attribute [local instance] Classical.propDecidable
variable {E M I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype I] [Fintype J]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {v : I → Set M}

theorem BasicData.exists_strict_terminal_cost_margin (b : BasicData (E := E) T Λ V)
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
      ∃ δ : ℝ, 0 < δ ∧ ∀ cost : centers → (Fin (N+1) → I) → J → ℝ,
        (∀ y labels j, cost y labels j ≤
          domainCoefficient Λ (BowenOpenCoverCoefficient.orbitBall T (N+1) radius y.val)
            (b.hyperbolic.localizedNativeCost d g N labels) + δ) →
        A * max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s) *
          (∑ y : centers, ∑ labels : Fin (N+1) → I, ∑ j : J, cost y labels j) < ρ^N := by
  obtain ⟨P,pressureP,ρ,radius,positiveρ,belowPressure,positiveRadius,N,positiveN,aboveMinimum,
    centers,p,captureP,compactPieces,insidePieces,coverPieces,δ,positiveδ,budget⟩ :=
      b.exists_strict_native_cost_margin forward inverse g continuous positive d capture
        positiveμ smallμ largeν positiveT negativeS (A * (Fintype.card J : ℝ))
        (mul_nonneg nonnegativeA (Nat.cast_nonneg _)) minimum
  refine ⟨P,pressureP,ρ,radius,positiveρ,belowPressure,positiveRadius,N,positiveN,aboveMinimum,
    centers,p,captureP,compactPieces,insidePieces,coverPieces,δ,positiveδ,?_⟩
  intro cost bound
  let q : centers → (Fin (N+1) → I) → ℝ := fun y labels =>
    domainCoefficient Λ (BowenOpenCoverCoefficient.orbitBall T (N+1) radius y.val)
      (b.hyperbolic.localizedNativeCost d g N labels) + δ
  have strict := budget q (fun _ _ => le_rfl)
  have total : (∑ y : centers, ∑ labels : Fin (N+1) → I, ∑ j : J, cost y labels j) ≤
      (Fintype.card J : ℝ) * ∑ y : centers, ∑ labels : Fin (N+1) → I, q y labels := by
    calc
      _ ≤ ∑ y : centers, ∑ labels : Fin (N+1) → I,
          (Fintype.card J : ℝ) * q y labels := by
        apply Finset.sum_le_sum
        intro y _
        apply Finset.sum_le_sum
        intro labels _
        have boundSum := Finset.sum_le_sum (s := (Finset.univ : Finset J))
          (fun j _ => bound y labels j)
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, q] using boundSum
      _ = _ := by simp only [Finset.mul_sum]
  let factor := max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s)
  have nonnegativeFactor : 0 ≤ A * factor :=
    mul_nonneg nonnegativeA ((Real.rpow_nonneg (by positivity) t).trans (le_max_left _ _))
  calc
    A * factor * (∑ y : centers, ∑ labels : Fin (N+1) → I, ∑ j : J, cost y labels j) ≤
        A * factor * ((Fintype.card J : ℝ) *
          ∑ y : centers, ∑ labels : Fin (N+1) → I, q y labels) :=
      mul_le_mul_of_nonneg_left total nonnegativeFactor
    _ = (A * (Fintype.card J : ℝ)) * factor *
        (∑ y : centers, ∑ labels : Fin (N+1) → I, q y labels) := by ring
    _ < ρ^N := strict

end LeanShared.HyperbolicBasicSet
