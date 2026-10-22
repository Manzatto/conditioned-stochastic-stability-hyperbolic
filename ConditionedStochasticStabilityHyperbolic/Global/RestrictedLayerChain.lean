module

public import ConditionedStochasticStabilityHyperbolic.Global.LayerOperators
public import ConditionedStochasticStabilityHyperbolic.Spectral.WeightedKernel
public import LeanShared.Probability.SubtypeKernel

/-!
# The actual recursively killed layer chain

Every measurable stratum of a strong-Feller chain has a canonical absorbing
chain with the exact restricted killed kernel. Its transfer is the bounded
layer diagonal constructed in LayerOperators. This permits successive Borel
splits of an adapted filtration without continuous zero-extension assumptions.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Global.RestrictedLayerChain

open ComplexStrongFeller LayerOperators

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (U : Set X) (hU : MeasurableSet U)

/-- A real absorbing chain, killed both by the original cemetery and on
exit from the specified Borel stratum. -/
def chain : AbsorbingMarkovChains.CanonicalChain U :=
  WeightedKernel.ofSubMarkov (LeanShared.SubtypeKernel.restrict C.killedTransition U hU)
    (LeanShared.SubtypeKernel.restrict_mass_le_one C.killedTransition U hU
      C.killedTransition_mass_le_one)

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
@[simp] theorem killedTransition :
    (chain C U hU).killedTransition =
      LeanShared.SubtypeKernel.restrict C.killedTransition U hU :=
  WeightedKernel.ofSubMarkov_killedTransition _ _

/-- Exact diagonal representation for any real or complex observable. -/
theorem integral_chain {𝕜 : Type*} [RCLike 𝕜] (f : U →ᵇ 𝕜) (x : U) :
    (∫ y, f y ∂(chain C U hU).killedTransition x) =
      extensionOperator C hSF U hU f x.val := by
  rw [killedTransition, extensionOperator_apply_subtype]
  rfl

omit [OpensMeasurableSpace X] in
include hSF in
/-- Strong-Feller regularity survives restriction to every measurable
stratum, even when its boundary is shared with other strata. -/
theorem strongFeller : HasStrongFellerKernel (chain C U hU) := by
  intro f hf hb
  obtain ⟨B, hB, hbound⟩ := hb
  let fext := zeroExtend U f
  have hfe : Measurable fext := measurable_zeroExtend U hU f hf
  have hbe : ∀ x, ‖fext x‖ ≤ B :=
    norm_zeroExtend_le U f hB (by simpa only [Real.norm_eq_abs] using hbound)
  have hc := (ComplexStrongFeller.continuous_integral C hSF fext hfe hB hbe).comp
    (continuous_subtype_val : Continuous (Subtype.val : U → X))
  convert hc using 1
  ext x
  rw [killedTransition]
  change (∫ y, f y ∂(C.killedTransition x.val).comap Subtype.val) =
    ∫ y, fext y ∂C.killedTransition x.val
  have he : U.indicator fext = fext := by
    funext y
    by_cases hy : y ∈ U
    · exact indicator_of_mem hy _
    · rw [indicator_of_notMem hy]
      exact (zeroExtend_of_not_mem U f y hy).symm
  calc
    _ = ∫ y : U, fext y.val ∂(C.killedTransition x.val).comap Subtype.val := by
      simp only [fext, zeroExtend_coe]
    _ = ∫ y in U, fext y ∂C.killedTransition x.val := integral_subtype_comap hU fext
    _ = _ := by rw [← integral_indicator hU, he]

/-- The recursively constructed chain produces exactly the lower diagonal
operator of the full killed chain. -/
theorem transferOperator_eq_lower {𝕜 : Type*} [RCLike 𝕜] :
    transferOperator (𝕜 := 𝕜) (chain C U hU) (strongFeller C hSF U hU) =
      lowerOperator (𝕜 := 𝕜) C hSF U hU := by
  ext f x
  exact integral_chain C hSF U hU f x

end ConditionedStochasticStabilityHyperbolic.Global.RestrictedLayerChain
