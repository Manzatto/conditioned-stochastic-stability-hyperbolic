module

public import LeanShared.Dynamics.BasicHyperbolicCodingPeriodicError
public import LeanShared.Dynamics.BasicHyperbolicCorePeriodicPoints

/-! The actual main coding periodic weights differ from the ORIGINAL
BasicData periodicPartitionSum by a strictly smaller exponential.  The
complete finite periodic point sets and the original energies are proved
identical through the invariant core, rather than supplied as sources.
-/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff Bundle NNReal BigOperators BoundedContinuousFunction
open ThermodynamicDefinitions BilateralShadowingCoding MarkovFinitePathRealization FiniteClosedRefinement

theorem BasicData.main_periodic_partition_exponential_error
    {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [TopologicalSpace J] [Fintype J]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (mixing : MixingOn T Λ)
    (ψ : M → ℝ) (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ)
    {d : ℕ} (C : Fin d → Set Λ) (closed : ∀ i, IsClosed (C i))
    (rectangles : J → Set Λ) (statuses : J ≃ (Fin d → Bool))
    (law : ∀ j, rectangles j = atom C (statuses j))
    (code : Path (Transition (invariantCoreHomeomorphism T Λ b.hyperbolic.invariant) rectangles) → Λ)
    (properties : MarkovCodingProperties (invariantCoreHomeomorphism T Λ b.hyperbolic.invariant) rectangles code) :
    let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
    let main := reindexedInteriorCode S C rectangles statuses law code
    ∃ P : ℝ, pressure T ψ Λ = (P : EReal) ∧ ∃ β D : ℝ,
      0 < β ∧ β < Real.exp P ∧ 0 < D ∧ ∀ n : ℕ,
        |bilateralPeriodicWeightSum ((fun x : Λ => ψ x.val) ∘ main) (n + 1) -
          b.periodicPartitionSum forward inverse ψ (n + 1)| ≤ D * β ^ (n + 1) := by
  obtain ⟨P, pressureP, β, D, positiveβ, smallerβ, positiveD, bound⟩ :=
    b.main_periodic_weight_exponential_error forward inverse mixing ψ α positiveα smallα regular
      C closed rectangles statuses law code properties
  refine ⟨P, pressureP, β, D, positiveβ, smallerβ, positiveD, ?_⟩
  intro n
  have result := bound n (b.corePeriodicPoints forward inverse (n + 1) (by omega))
    (b.mem_corePeriodicPoints forward inverse (n + 1) (by omega))
  rw [b.core_periodic_weight_sum forward inverse ψ (n + 1) (by omega)] at result
  exact result

end LeanShared.HyperbolicBasicSet
