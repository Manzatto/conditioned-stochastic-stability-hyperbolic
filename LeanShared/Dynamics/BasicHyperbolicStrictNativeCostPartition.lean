module
public import LeanShared.Dynamics.BasicHyperbolicStrictNativeCostCover
public import LeanShared.Geometry.FiniteSmoothCapturePartition

/-! The actual strict native-cost core cover yields smooth pressure-center
cutoffs and compact core pieces inside the original Bowen balls. The
principal budget is unchanged: each old center is charged exactly once. -/
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

theorem BasicData.exists_strict_native_cost_partition (b : BasicData (E := E) T Λ V)
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
      A * max ((10*μ^N)^t) (((4*(ν⁻¹)^N)⁻¹)^s) *
        (∑ x ∈ centers, ∑ labels : Fin (N+1) → I,
          domainCoefficient Λ (BowenOpenCoverCoefficient.orbitBall T (N+1) radius x)
            (b.hyperbolic.localizedNativeCost d g N labels)) < ρ^N := by
  obtain ⟨P,pressureP,ρ,radius,positiveρ,belowPressure,positiveRadius,N,positiveN,aboveMinimum,
    centers,_separated,openBalls,cover,strict⟩ := b.exists_strict_native_cost_cover forward inverse
      g continuous positive d capture positiveμ smallμ largeν positiveT negativeS A nonnegativeA minimum
  let p := FiniteSmoothCapturePartition.data (E := E) Λ b.hyperbolic.compact
    (fun y : centers => BowenOpenCoverCoefficient.orbitBall T (N+1) radius y.val)
  have selectedCover : Λ ⊆ ⋃ y : centers, BowenOpenCoverCoefficient.orbitBall T (N+1) radius y.val := by
    intro x hx
    obtain ⟨y,hy,inside⟩ := mem_iUnion₂.mp (cover hx)
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,inside⟩
  have captureP : Λ ⊆ p.capture := p.reference (fun y => openBalls y.val) selectedCover
  refine ⟨P,pressureP,ρ,radius,positiveρ,belowPressure,positiveRadius,N,positiveN,aboveMinimum,
    centers,p,captureP,?_,?_,?_,strict⟩
  · intro y
    exact b.hyperbolic.compact.inter_right (isClosed_tsupport _)
  · intro y x hx
    exact p.support y hx.2
  · intro x hx
    have one := p.one x (captureP hx)
    have nonzero : ∃ y : centers, p.beta y x ≠ 0 := by
      by_contra none
      have zero : ∀ y : centers, p.beta y x = 0 := by simpa only [not_exists, not_not] using none
      simp only [zero, Finset.sum_const_zero] at one
      exact zero_ne_one one
    obtain ⟨y,nonzero⟩ := nonzero
    exact mem_iUnion.mpr ⟨y,hx,subset_tsupport _ nonzero⟩

end LeanShared.HyperbolicBasicSet
