module

public import ConditionedStochasticStabilityHyperbolic.Spectral.RegularCoreApproximation
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Actual regular and anisotropic multipliers from the common smooth core

Multiplication by a smooth test function preserves the common smooth core.
The classical ordinary Hölder and anisotropic multiplication norm bounds
construct the regular and analytic multipliers on their completions. The
whole regular-space physical and analytic compatibility laws are proved
by density from literal smooth-core multiplication; they are not fields
asserting the desired probability integral or the noisy eigenvector product.

The regular space with this dense smooth core is the little `C^u`
completion. A `C^{r-1}` noisy smoothing output lies in it because `u<r-1`.
Big `C^u` must not be given a false dense smooth-core hypothesis.
-/

@[expose] public noncomputable section

open Set
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.ConstructedRegularMultipliers

open RegularCoreApproximation

variable {Reg A Core X : Type*}
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
  [AddCommGroup Core] [Module ℂ Core] [TopologicalSpace X]
  (D : Realization (Reg := Reg) (A := A) (Core := Core) (X := X))
  (q : Core →ₗ[ℂ] Reg) (hqcore : ∀ c, q c = D.smooth c)
  (qa : Core →ₗ[ℂ] A) (hqa : DenseRange qa)
  (haCore : ∀ c, D.analytic (D.smooth c) = qa c)
  (multiply : Core →ₗ[ℂ] Core) (h : X →ᵇ ℝ)
  (hphysicalCore : ∀ c, D.physical (D.smooth (multiply c)) =
    D.physical (D.smooth c) * AbsorbingMarkovChains.ComplexKernel.ofReal h)
  (CR CA : ℝ) (hCR : 0 ≤ CR) (hCA : 0 ≤ CA)
  (hregularBound : ∀ c, ‖q (multiply c)‖ ≤ CR * ‖q c‖)
  (hanalyticBound : ∀ c, ‖qa (multiply c)‖ ≤ CA * ‖qa c‖)

include hqcore in
omit [CompleteSpace Reg] [CompleteSpace A] in
theorem regular_core_dense : DenseRange q := by
  have heq : (fun c => q c) = D.smooth := funext hqcore
  change DenseRange (fun c => q c)
  rw [heq]
  exact D.dense

def regularMultiplier : Reg →L[ℂ] Reg := (q.comp multiply).extendOfNorm q

def analyticMultiplier : A →L[ℂ] A := (qa.comp multiply).extendOfNorm qa

include hqcore hregularBound in
omit [CompleteSpace A] in
theorem regularMultiplier_core (c : Core) :
    regularMultiplier q multiply (D.smooth c) = D.smooth (multiply c) := by
  rw [← hqcore c, ← hqcore (multiply c)]
  exact LinearMap.extendOfNorm_eq (f := q.comp multiply) (e := q)
    (regular_core_dense D q hqcore) ⟨CR, hregularBound⟩ c

include hqa hanalyticBound in
theorem analyticMultiplier_core (c : Core) : analyticMultiplier qa multiply (qa c) = qa (multiply c) :=
  LinearMap.extendOfNorm_eq (f := qa.comp multiply) (e := qa) hqa ⟨CA, hanalyticBound⟩ c

include hqcore hregularBound hphysicalCore in
omit [CompleteSpace A] in
theorem physical_multiplier_law (v : Reg) :
    D.physical (regularMultiplier q multiply v) =
      D.physical v * AbsorbingMarkovChains.ComplexKernel.ofReal h := by
  refine D.dense.induction_on
    (p := fun v => D.physical (regularMultiplier q multiply v) =
      D.physical v * AbsorbingMarkovChains.ComplexKernel.ofReal h) v
    (isClosed_eq (D.physical.continuous.comp (regularMultiplier q multiply).continuous)
      (D.physical.continuous.mul continuous_const)) ?_
  intro c
  rw [regularMultiplier_core D q hqcore multiply CR hregularBound]
  exact hphysicalCore c

include hqcore hregularBound hqa hanalyticBound haCore in
theorem analytic_multiplier_law :
    D.analytic.comp (regularMultiplier q multiply) = (analyticMultiplier qa multiply).comp D.analytic := by
  apply ContinuousLinearMap.ext
  intro v
  refine D.dense.induction_on
    (p := fun v => D.analytic (regularMultiplier q multiply v) = analyticMultiplier qa multiply (D.analytic v)) v
    (isClosed_eq (D.analytic.continuous.comp (regularMultiplier q multiply).continuous)
      ((analyticMultiplier qa multiply).continuous.comp D.analytic.continuous)) ?_
  intro c
  rw [regularMultiplier_core D q hqcore multiply CR hregularBound, haCore, haCore,
    analyticMultiplier_core qa hqa multiply CA hanalyticBound]

include hqcore hregularBound hCR in
omit [CompleteSpace A] in
theorem regular_multiplier_norm : ‖regularMultiplier q multiply‖ ≤ CR :=
  LinearMap.opNorm_extendOfNorm_le (regular_core_dense D q hqcore) hCR hregularBound

include hqa hanalyticBound hCA in
theorem analytic_multiplier_norm : ‖analyticMultiplier qa multiply‖ ≤ CA :=
  LinearMap.opNorm_extendOfNorm_le hqa hCA hanalyticBound

end ConditionedStochasticStabilityHyperbolic.ConstructedRegularMultipliers
