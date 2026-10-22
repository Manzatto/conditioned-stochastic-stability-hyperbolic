module

public import ConditionedStochasticStabilityHyperbolic.Global.AllShiftNullBoundaryFiltration
public import AbsorbingMarkovChains.CanonicalChain
public import LeanShared.MeasureTheory.ForwardNullReference

/-! An auxiliary reference is used only to express kernel densities and
boundary nullity. The analytic spaces and smooth reference remain unchanged. -/

public noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Global.BoundaryNullDensityReference
open LeanShared ShiftedFiltrationGeometry
variable {X I : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] in
theorem positive_boundary (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X)
    (ℓ : ℕ) (D : AdaptedSource T A Λ ℓ) (σ : Measure X)
    (null : ∀ N j, 0 < j → j ≤ ℓ →
      σ (frontier (levels T A Λ ℓ N D j)) = 0)
    (j : ℕ) (positive : 0 < j) (bound : j ≤ ℓ) :
    ForwardNullReference.reference T σ (frontier (D.levels j)) = 0 := by
  apply (ForwardNullReference.null_iff T T.measurableEmbedding σ _).mpr
  intro N
  have ready := null N j positive bound
  rw [levels, shiftedFiltration_pos T N A D.levels positive,
    ← ShiftedBoundaryGeometry.preimage_iterate_frontier] at ready
  exact ready

omit [CompactSpace X] in
theorem eventually_density (T : X ≃ₜ X) (σ : Measure X) [IsFiniteMeasure σ]
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain X)
    (density : ℝ≥0 → X × X → ENNReal)
    (actual : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ x,
      (C ε).killedTransition x = σ.withDensity (fun y => density ε (x, y))) :
    ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ x,
      (C ε).killedTransition x = (ForwardNullReference.reference T σ).withDensity
        (fun y => ((C ε).killedTransition x).rnDeriv
          (ForwardNullReference.reference T σ) y) := by
  filter_upwards [actual] with ε identity
  intro x
  have : IsFiniteMeasure ((C ε).killedTransition x) := by
    change IsFiniteMeasure ((C ε).toKilledKernel.kernel x)
    infer_instance
  apply (ForwardNullReference.density_transport T T.measurableEmbedding σ _ ?_).symm
  rw [identity x]
  exact withDensity_absolutelyContinuous σ _

end ConditionedStochasticStabilityHyperbolic.Global.BoundaryNullDensityReference
