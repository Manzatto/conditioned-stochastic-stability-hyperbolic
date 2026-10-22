module

public import ConditionedStochasticStabilityHyperbolic.Global.LivePrefixQuasiErgodic

/-! # Exact live-state bounded-measurable conditioned statistics

A live observable extends measurably by zero to the ambient state space.
The actual canonical conditioned averages agree at every horizon. Thus the
constructed ambient basin limits give the literal live-process limits,
including for subordinate HG2 prefixes with no global ambient spectral gap.
-/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.Global.LivePrefixPathAverage
open AbsorbingMarkovChains RestrictedLayerChain PrefixCorrespondence ComplexStrongFeller
variable {X : Type*} [MeasurableSpace X]

theorem pathAverage_live_eq_ambient_zeroExtension
    (C : CanonicalChain X) (U : Set X) (hU : MeasurableSet U)
    (hsupport : ∀ x ∈ U, C.killedTransition x Uᶜ = 0)
    (f : U → ℝ) (hf : Measurable f) (hb : ∃ B : ℝ, ∀ y, ‖f y‖ ≤ B)
    (x : U) :
    MeasurableCanonical.pathAverage (chain C U hU) f x =
      MeasurableCanonical.pathAverage C (zeroExtend U f) x.val := by
  obtain ⟨B, hB⟩ := hb
  have hbf : ∀ y, ‖zeroExtend U f y‖ ≤ max B 0 :=
    norm_zeroExtend_le U f (le_max_right B 0) (fun y => (hB y).trans (le_max_left B 0))
  funext n
  have he := conditioned_average_eq C U hU hsupport (zeroExtend U f)
    (measurable_zeroExtend U hU f hf) (max B 0) (le_max_right B 0) hbf n x
  have hrestrict : (fun y : U => zeroExtend U f y.val) = f := by
    funext y
    exact zeroExtend_coe U f y
  rw [hrestrict] at he
  exact he

/-- The corresponding mean is the exact same mean under state inclusion. -/
theorem integral_zeroExtension_map (U : Set X) (hU : MeasurableSet U)
    (ν : Measure U) (f : U → ℝ) :
    (∫ y, zeroExtend U f y ∂ν.map Subtype.val) = ∫ y, f y ∂ν := by
  rw [(MeasurableEmbedding.subtype_coe hU).integral_map]
  congr 1
  funext y
  exact zeroExtend_coe U f y

end ConditionedStochasticStabilityHyperbolic.Global.LivePrefixPathAverage
