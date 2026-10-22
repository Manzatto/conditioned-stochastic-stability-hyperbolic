module

public import AbsorbingMarkovChains.CemeteryBridge

/-! # The killed kernel determines the genuine absorbing chain

Probability normalization forces cemetery mass, and the cemetery is absorbing.
Consequently equal killed kernels give equal canonical path laws and all
conditioned-process notions, rather than only equal transfer operators.
-/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace ConditionedStochasticStabilityHyperbolic
variable {X : Type*} [MeasurableSpace X]

 theorem canonicalChain_eq_of_killedTransition_eq
    (C D : AbsorbingMarkovChains.CanonicalChain X)
    (h : C.killedTransition = D.killedTransition) : C = D := by
  have hl (x : X) (S : Set (Option X)) (hS : MeasurableSet S) (hn : none ∉ S) :
      C.transition (some x) S = D.transition (some x) S := by
    have he : S = Option.some '' (Option.some ⁻¹' S) := by
      ext y
      cases y with
      | none => simp only [mem_image, Option.some_ne_none, and_false, exists_false, iff_false]; exact hn
      | some y => simp
    rw [he, ← C.killedTransition_apply x _ (hS.preimage AbsorbingMarkovChains.measurable_some_state),
      ← D.killedTransition_apply x _ (hS.preimage AbsorbingMarkovChains.measurable_some_state), h]
  have ht : C.transition = D.transition := by
    ext x S hS
    cases x with
    | none => rw [C.absorbing, D.absorbing]
    | some x =>
      by_cases hn : none ∈ S
      · have hc := hl x Sᶜ hS.compl (by simpa only [mem_compl_iff, not_not] using hn)
        have heC := prob_compl_eq_one_sub (μ := C.transition (some x)) hS.compl
        have heD := prob_compl_eq_one_sub (μ := D.transition (some x)) hS.compl
        simpa only [compl_compl] using heC.trans ((congrArg (fun z => 1 - z) hc).trans heD.symm)
      · exact hl x S hS hn
  cases C
  cases D
  cases ht
  rfl

end ConditionedStochasticStabilityHyperbolic
