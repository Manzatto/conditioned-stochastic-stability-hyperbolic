module

public import LeanShared.Geometry.SupportedPairingClosedCore
public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexStrongFeller
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedNoise

/-! # Actual cutoff transfer outputs lie in the closed supported regular core

The support conclusion follows from the departure weight in the actual killed
kernel. No regularity improvement from continuous to differentiable functions
and no full reference support are needed.
-/
@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.CutoffClosedCoreRange

variable {M Ω : Type*} [MeasurableSpace M] [MeasurableSpace Ω]
  (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : M × Ω → M) (hF : Measurable F)
  (K : Set M) (hK : MeasurableSet K) (w : K → ℝ) (hw : Measurable w)
  (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)

theorem killedTransition_eq_zero_of_weight_zero (x : K) (hx : w x = 0) :
    (RestrictedNoise.chain ρ F hF K hK w hw R hR hwR).killedTransition x = 0 := by
  rw [RestrictedNoise.killedTransition,
    LeanShared.WeightedConditioning.normalizedKernel,
    LeanShared.WeightedConditioning.realWeightedKernel_apply, hx]
  simp

variable [MetricSpace M] [BorelSpace M]
  (sf : HasStrongFellerKernel (RestrictedNoise.chain ρ F hF K hK w hw R hR hwR))

theorem transfer_eq_zero_of_weight_zero (f : K →ᵇ ℂ) (x : K) (hx : w x = 0) :
    ComplexStrongFeller.transferOperator
      (RestrictedNoise.chain ρ F hF K hK w hw R hR hwR) sf f x = 0 := by
  rw [ComplexStrongFeller.transferOperator_apply,
    killedTransition_eq_zero_of_weight_zero ρ F hF K hK w hw R hR hwR x hx,
    integral_zero_measure]

theorem raw_transfer_tsupport_subset (a : ℂ) (f : K →ᵇ ℂ) :
    tsupport ((a • ComplexStrongFeller.transferOperator
      (RestrictedNoise.chain ρ F hF K hK w hw R hR hwR) sf) f) ⊆ tsupport w := by
  apply closure_mono
  intro x hx
  change w x ≠ 0
  intro hzero
  apply hx
  change a • ComplexStrongFeller.transferOperator
    (RestrictedNoise.chain ρ F hF K hK w hw R hR hwR) sf f x = 0
  rw [transfer_eq_zero_of_weight_zero ρ F hF K hK w hw R hR hwR sf f x hzero,
    smul_zero]

variable {E Reg : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompactSpace K]
  {V : Set M}

/-- Every actual cutoff output lies in the Banach closure of the supported
regular core, by its departure support and supported smooth approximation. -/
theorem raw_transfer_mem_closedCore
    (q : LeanShared.SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ] Reg)
    (physical : Reg →L[ℂ] (K →ᵇ ℂ))
    (hphysical : ∀ c, physical (q c) =
      LeanShared.SmoothSupportedManifoldCore.physicalCore V K c)
    (hKclosed : IsClosed K) (hV : IsOpen V)
    (hwSupport : tsupport w ⊆ {x : K | x.val ∈ V})
    (a : ℂ) (f : K →ᵇ ℂ) :
    (a • ComplexStrongFeller.transferOperator
      (RestrictedNoise.chain ρ F hF K hK w hw R hR hwR) sf) f ∈
      LeanShared.SupportedPairingClosedCore.space physical :=
  LeanShared.SmoothSupportedManifoldCore.mem_physical_closedCore_of_tsupport
    q physical hphysical hKclosed hV _
    ((raw_transfer_tsupport_subset ρ F hF K hK w hw R hR hwR sf a f).trans hwSupport)

end ConditionedStochasticStabilityHyperbolic.CutoffClosedCoreRange
