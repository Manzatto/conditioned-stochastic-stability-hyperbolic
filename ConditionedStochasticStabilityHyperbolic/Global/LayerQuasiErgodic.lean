module

public import ConditionedStochasticStabilityHyperbolic.Global.LayerRankOne
public import ConditionedStochasticStabilityHyperbolic.Spectral.PositiveEigenmeasure
public import ConditionedStochasticStabilityHyperbolic.Spectral.QuasiErgodic

/-!
# Actual global QEM constructed from dominant-layer spectral data

The Riesz left measure, nonnegative eigenfunction, product probability and
bounded-measurable conditioned limits are derived from the global data
produced by the bounded-layer construction. Neither a global spectral gap
nor a leading measure is assumed by the dominant-layer applications.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Global.LayerQuasiErgodic

open ComplexStrongFeller LayerRankOne LayerOperators

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)

local instance killedKernelFinite : IsFiniteKernel C.killedTransition :=
  ⟨⟨1, by simp, C.killedTransition_mass_le_one⟩⟩

/-- The global leading measure is constructed by Riesz representation. -/
def leadingMeasure
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ)) : Measure X :=
  d.eigenmeasure (actual_transfer_positive C hSF)

instance leadingMeasure_isFinite
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ)) :
    IsFiniteMeasure (leadingMeasure C hSF d) := by
  unfold leadingMeasure
  infer_instance

/-- The literal global limiting product probability. -/
def productMeasure
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ)) : Measure X :=
  LeanShared.eigenvectorMeasure (leadingMeasure C hSF d) d.eigenvector

/-- Full bounded-measurable QEM existence; Riesz and eigenfunction
nonnegativity are produced internally from positivity of the actual kernel. -/
theorem productMeasure_isQuasiErgodic
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ)) :
    C.IsQuasiErgodic (productMeasure C hSF d) := by
  exact QuasiErgodic.eigenvectorMeasure_isQuasiErgodic_of_strongFeller C
    (transferOperator C hSF) (transferOperator_apply C hSF) d (leadingMeasure C hSF d)
    (d.eigenmeasure_represents (actual_transfer_positive C hSF))
    (d.eigenvector_nonneg_of_positive (actual_transfer_positive C hSF)) hSF

/-- Actual global conditioned averages converge at every state in the
constructed positive basin, for every bounded measurable observable. -/
theorem conditioned_average_limit
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ))
    (h : X → ℝ) (hh : Measurable h) (hb : ∃ B : ℝ, ∀ x, ‖h x‖ ≤ B)
    (x : X) (hx : 0 < d.eigenvector x) :
    Tendsto (MeasurableCanonical.pathAverage C h x) atTop
      (𝓝 (∫ y, h y ∂productMeasure C hSF d)) := by
  obtain ⟨s⟩ := exists_smoothedObservable C hSF h hh hb
  obtain ⟨B, hB⟩ := hb
  have hprod : Integrable (fun y => h y * d.eigenvector y) (leadingMeasure C hSF d) := by
    apply Integrable.of_bound (hh.mul d.eigenvector.continuous.measurable).aestronglyMeasurable
      (max B 0 * ‖d.eigenvector‖)
    apply ae_of_all
    intro y
    change ‖h y * d.eigenvector y‖ ≤ max B 0 * ‖d.eigenvector‖
    rw [norm_mul]
    exact mul_le_mul ((hB y).trans (le_max_left _ _))
      (d.eigenvector.norm_coe_le_norm y) (norm_nonneg _) (le_max_right _ _)
  have hleft := rankOne_integral_kernel d C.killedTransition (transferOperator_apply C hSF)
    (leadingMeasure C hSF d) (d.eigenmeasure_represents (actual_transfer_positive C hSF)) _ hprod
  exact (canonical_measurable_average_limit C (transferOperator_apply C hSF) d
    (leadingMeasure C hSF d) (d.eigenmeasure_represents (actual_transfer_positive C hSF))
    (d.eigenvector_nonneg_of_positive (actual_transfer_positive C hSF)) s hleft x hx).2

/-- A dominant actual upper diagonal and pressure-small lower aggregate
construct a global QEM; no preexisting global measure or gap is an input. -/
theorem qem_from_dominant_upper_layer
    (L : Set X) (hL : MeasurableSet L)
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    (d : RankOneSpectralData (upperOperator (𝕜 := ℝ) C hSF L hL)
      (1 : (Lᶜ : Set X) →ᵇ ℝ))
    {CA β : ℝ} (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖lowerOperator (𝕜 := ℝ) C hSF L hL ^ n‖ ≤ CA * β ^ n) :
    C.IsQuasiErgodic (productMeasure C hSF
      (globalDataWithSubordinateLower C hSF L hL hsupport d hCA hβ hβr hA)) :=
  productMeasure_isQuasiErgodic C hSF _

/-- Extending a dominant actual lower aggregate by an upper aggregate of
smaller pressure constructs a global QEM. Subordinate mixing is unnecessary. -/
theorem qem_from_dominant_lower_layer
    (L : Set X) (hL : MeasurableSet L)
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    (d : RankOneSpectralData (lowerOperator (𝕜 := ℝ) C hSF L hL) (1 : L →ᵇ ℝ))
    {CA β : ℝ} (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖upperOperator (𝕜 := ℝ) C hSF L hL ^ n‖ ≤ CA * β ^ n) :
    C.IsQuasiErgodic (productMeasure C hSF
      (globalDataWithSubordinateUpper C hSF L hL hsupport d hCA hβ hβr hA)) :=
  productMeasure_isQuasiErgodic C hSF _

end ConditionedStochasticStabilityHyperbolic.Global.LayerQuasiErgodic
