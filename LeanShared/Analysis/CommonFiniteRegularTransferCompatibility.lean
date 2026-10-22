module

public import LeanShared.Analysis.FiniteRegularTransferBetweenSpaces

/-!
# Compatibility of actual transfers on two completed norms

The actual weighted core function has high regularity `C^{r-1}` but its
noise orbit is only required to be continuous in `C^beta`, with the weak
positive exponent less than `beta<r-1`. Classical downgrade preserves
the represented function. A common global smooth approximation identifies
the strong realization, mapped to the weak completion, with the lower
regularity weak realization. Density then proves compatibility of the
constructed strong and rectangular completed transfer operators.

No equality of completed operators or supplied mixed-norm compatibility
is an input. The classical function embeddings and common atlas smooth
approximation are the contracts of BT2008 Lemma 4.6 and its following
completion definition; the canonical inclusion's smooth-core identity is
already proved by the physical completion constructors.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace LeanShared.CommonFiniteRegularTransferCompatibility

open DyadicCompletion FiniteRegularTransferRealization

variable {X Ω Core VS VH VW High Low : Type*}
  [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup VS] [NormedSpace ℂ VS] [CompleteSpace VS]
  [NormedAddCommGroup VH] [NormedSpace ℂ VH]
  [NormedAddCommGroup VW] [NormedSpace ℂ VW] [CompleteSpace VW]
  [NormedAddCommGroup High] [NormedSpace ℂ High]
  [NormedAddCommGroup Low] [NormedSpace ℂ Low]
  (qS : Core →ₗ[ℂ] VS) (qH : Core →ₗ[ℂ] VH) (qW : Core →ₗ[ℂ] VW)
  (smooth : Core →ₗ[ℂ] (X → ℂ))
  (viewHigh : High →ₗ[ℂ] (X → ℂ)) (hinjHigh : Function.Injective viewHigh)
  (viewLow : Low →ₗ[ℂ] (X → ℂ)) (hinjLow : Function.Injective viewLow)
  (downgrade : High →L[ℂ] Low)
  (hview : ∀ f, viewLow (downgrade f) = viewHigh f)
  (F : Ω → X → X) (g : X → ℝ)
  (hhigh : ∀ a c, weightedComposition (F a) g (smooth c) ∈ viewHigh.range)
  (hlow : ∀ a c, weightedComposition (F a) g (smooth c) ∈ viewLow.range)

include hview in
theorem regularAction_downgrade (a : Ω) (c : Core) :
    downgrade (regularAction smooth High viewHigh hinjHigh F g hhigh a c) =
      regularAction smooth Low viewLow hinjLow F g hlow a c := by
  apply hinjLow
  rw [hview]
  ext x
  rw [regularAction_apply, regularAction_apply]

variable (realizeStrong : High →L[ℂ] closedCore qS)
  (realizeWeak : Low →L[ℂ] closedCore qW)
  (i : closedCore qS →L[ℂ] closedCore qH) (j : closedCore qS →L[ℂ] closedCore qW)
  (hi : ∀ c, i (coreLift qS c) = coreLift qH c)
  (hj : ∀ c, j (coreLift qS c) = coreLift qW c)
  (approximation : High → ℕ → Core)
  (happroxStrong : ∀ f, Tendsto (fun n => coreLift qS (approximation f n)) atTop (𝓝 (realizeStrong f)))
  (happroxWeak : ∀ f, Tendsto (fun n => coreLift qW (approximation f n)) atTop
    (𝓝 (realizeWeak (downgrade f))))

include hj happroxStrong happroxWeak in
omit [CompleteSpace VS] [CompleteSpace VW] in
theorem realization_compatibility (f : High) :
    j (realizeStrong f) = realizeWeak (downgrade f) := by
  have ht : Tendsto (fun n => coreLift qW (approximation f n)) atTop
      (𝓝 (j (realizeStrong f))) := by
    simpa only [Function.comp_def, hj] using j.continuous.tendsto (realizeStrong f) |>.comp (happroxStrong f)
  exact tendsto_nhds_unique ht (happroxWeak f)

variable (LS LW : ℝ)
  (hstrong : ∀ a c,
    ‖FiniteRegularTransferRealization.targetCore qS smooth High viewHigh hinjHigh realizeStrong F g hhigh a c‖ ≤
      LS * ‖qS c‖)
  (hweak : ∀ a c,
    ‖FiniteRegularTransferBetweenSpaces.targetCore smooth Low viewLow hinjLow realizeWeak F g hlow a c‖ ≤
      LW * ‖qH c‖)

include hview hi hj happroxStrong happroxWeak hstrong hweak in
theorem operator_compatibility (a : Ω) :
    (FiniteRegularTransferBetweenSpaces.operator qH smooth Low viewLow hinjLow realizeWeak F g hlow a).comp i =
      j.comp (FiniteRegularTransferRealization.operator qS smooth High viewHigh hinjHigh realizeStrong F g hhigh a) := by
  apply ContinuousLinearMap.ext
  intro x
  refine (coreLift_dense qS).induction_on
    (p := fun x => FiniteRegularTransferBetweenSpaces.operator qH smooth Low viewLow hinjLow realizeWeak F g hlow a
      (i x) = j (FiniteRegularTransferRealization.operator qS smooth High viewHigh hinjHigh realizeStrong F g hhigh a x))
    x (isClosed_eq
      ((FiniteRegularTransferBetweenSpaces.operator qH smooth Low viewLow hinjLow realizeWeak F g hlow a).continuous.comp i.continuous)
      (j.continuous.comp (FiniteRegularTransferRealization.operator qS smooth High viewHigh hinjHigh realizeStrong F g hhigh a).continuous)) ?_
  intro c
  rw [hi, FiniteRegularTransferBetweenSpaces.operator_core qH smooth Low viewLow hinjLow realizeWeak F g hlow LW hweak,
    FiniteRegularTransferRealization.operator_core qS smooth High viewHigh hinjHigh realizeStrong F g hhigh LS hstrong,
    realization_compatibility qS qW downgrade realizeStrong realizeWeak j hj approximation happroxStrong happroxWeak,
    regularAction_downgrade smooth viewHigh hinjHigh viewLow hinjLow downgrade hview F g hhigh hlow]

end LeanShared.CommonFiniteRegularTransferCompatibility
