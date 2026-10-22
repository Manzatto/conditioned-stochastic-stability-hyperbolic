module

public import LeanShared.Probability.DensitySmoothing
public import LeanShared.Probability.DensityCompactTransfer
public import ConditionedStochasticStabilityHyperbolic.Spectral.StrongFeller
public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexStrongFeller

/-! # Producing the strong-Feller input from the actual transition density

The classical noise-density formula, its boundedness and continuity in the
departure state suffice. Strong-Feller regularity is derived rather than
supplied independently alongside the same density data.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace ConditionedStochasticStabilityHyperbolic.DensityStrongFeller

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace X]

theorem of_bounded_continuous_density
    (C : AbsorbingMarkovChains.CanonicalChain X) (σ : Measure X) [IsFiniteMeasure σ]
    (q : X × X → ℝ) (hq : Measurable q) (hq0 : ∀ x y, 0 ≤ q (x, y))
    (hC : ∀ x, C.killedTransition x = σ.withDensity (fun y => ENNReal.ofReal (q (x, y))))
    (M : ℝ) (hM : 0 ≤ M) (hqM : ∀ x y, ‖q (x, y)‖ ≤ M)
    (hc : ∀ᵐ y ∂σ, Continuous (fun x => q (x, y))) : HasStrongFellerKernel C := by
  intro f hf hbound
  obtain ⟨B, _hB, hb⟩ := hbound
  exact LeanShared.DensitySmoothing.continuous_integral_of_bounded_density
    C.killedTransition σ q hq hq0 hC M hM hqM hc f hf B hb

end ConditionedStochasticStabilityHyperbolic.DensityStrongFeller

namespace ConditionedStochasticStabilityHyperbolic.DensityStrongFeller

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The same actual density gives a compact complex transfer, stronger than
the square-compactness input used by spectral comparison. -/
theorem compact_complex_transfer_of_density
    (C : AbsorbingMarkovChains.CanonicalChain Y) (hSF : HasStrongFellerKernel C)
    (σ : Measure Y) [IsFiniteMeasure σ]
    (q : Y × Y → ℝ) (hq : Measurable q) (hq0 : ∀ x y, 0 ≤ q (x, y))
    (hC : ∀ x, C.killedTransition x = σ.withDensity (fun y => ENNReal.ofReal (q (x, y))))
    (M : ℝ) (hM : 0 ≤ M) (hqM : ∀ x y, ‖q (x, y)‖ ≤ M)
    (hc : ∀ᵐ y ∂σ, Continuous (fun x => q (x, y))) :
    IsCompactOperator (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) := by
  apply LeanShared.DensityCompactTransfer.compact_of_bounded_continuous_density
    _ σ q hq M hM hqM hc
  intro f x
  rw [ComplexStrongFeller.transferOperator_apply, hC x,
    integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (hq0 x _)]
  · exact (hq.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  · exact Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)

theorem square_compact_complex_transfer_of_density
    (C : AbsorbingMarkovChains.CanonicalChain Y) (hSF : HasStrongFellerKernel C)
    (σ : Measure Y) [IsFiniteMeasure σ]
    (q : Y × Y → ℝ) (hq : Measurable q) (hq0 : ∀ x y, 0 ≤ q (x, y))
    (hC : ∀ x, C.killedTransition x = σ.withDensity (fun y => ENNReal.ofReal (q (x, y))))
    (M : ℝ) (hM : 0 ≤ M) (hqM : ∀ x y, ‖q (x, y)‖ ≤ M)
    (hc : ∀ᵐ y ∂σ, Continuous (fun x => q (x, y))) :
    IsCompactOperator (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF ^ 2 :
      (BoundedContinuousFunction Y ℂ) →L[ℂ] (BoundedContinuousFunction Y ℂ)) := by
  have hp := compact_complex_transfer_of_density C hSF σ q hq hq0 hC M hM hqM hc
  rw [pow_two]
  exact hp.comp_clm (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)

end ConditionedStochasticStabilityHyperbolic.DensityStrongFeller
