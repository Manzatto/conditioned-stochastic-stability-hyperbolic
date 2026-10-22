module
public import LeanShared.Dynamics.BasicHyperbolicLocalizedCostGrowth
public import LeanShared.Dynamics.BasicHyperbolicSeparatedSpanning

/-! Actual finite open Bowen covers of the core have the pressure-controlled
sum of localized native principal costs. The centers and cover are
constructed, rather than supplied as a pressure-source field. -/
@[expose] public noncomputable section
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

theorem BasicData.eventual_native_cost_open_cover (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (g : M → ℝ) (continuous : ContinuousOn g Λ) (positive : ∀ x ∈ Λ, 0 < g x)
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ v) (capture : Λ ⊆ d.capture) :
    ∃ P : ℝ, pressure T (b.hyperbolic.potential g) Λ = (P : EReal) ∧
      ∀ ε : ℝ, 0 < ε → ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
        ∀ᶠ N : ℕ in atTop, ∃ centers : Finset M,
          Separated T Λ (N+1) ρ centers ∧
          (∀ x, IsOpen (BowenOpenCoverCoefficient.orbitBall T (N+1) ρ x)) ∧
          (Λ ⊆ ⋃ x ∈ centers, BowenOpenCoverCoefficient.orbitBall T (N+1) ρ x) ∧
          (∑ x ∈ centers, ∑ labels : Fin (N+1) → I,
            domainCoefficient Λ (BowenOpenCoverCoefficient.orbitBall T (N+1) ρ x)
              (b.hyperbolic.localizedNativeCost d g N labels)) ≤
            C * Real.exp ((N : ℝ) * (P+ε)) := by
  obtain ⟨P,pressureP,growth⟩ := b.eventual_localized_native_cost_growth forward inverse
    g continuous positive d capture
  refine ⟨P,pressureP,fun ε positiveε => ?_⟩
  obtain ⟨ρ,C,positiveρ,positiveC,costs⟩ := growth ε positiveε
  refine ⟨ρ,C,positiveρ,positiveC,?_⟩
  filter_upwards [costs] with N cost
  obtain ⟨centers,separated,spans⟩ := b.exists_separated_spanning forward inverse (N+1) ρ positiveρ
  refine ⟨centers,separated,?_,?_,cost centers separated⟩
  · intro x
    have representation : BowenOpenCoverCoefficient.orbitBall T (N+1) ρ x =
        ⋂ j : Fin (N+1), {y | dist ((T : M → M)^[j.val] y) ((T : M → M)^[j.val] x) < ρ} := by
      ext y
      simp only [BowenOpenCoverCoefficient.orbitBall,mem_ofPred_eq,mem_iInter]
      exact ⟨fun near j => near j.val j.isLt,fun near j hj => near ⟨j,hj⟩⟩
    rw [representation]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt
      ((T.continuous.iterate j.val).dist continuous_const) continuous_const)
  · intro y hy
    obtain ⟨x,hx,close⟩ := spans y hy
    exact mem_iUnion₂.mpr ⟨x,hx,close⟩

end LeanShared.HyperbolicBasicSet
