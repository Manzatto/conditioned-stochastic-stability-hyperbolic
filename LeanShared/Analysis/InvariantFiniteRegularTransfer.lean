module

public import LeanShared.Analysis.FiniteRegularTransferRealization
public import LeanShared.Analysis.AnnealedOperatorBounds

/-!
# Constructed invariant finite-regular transfer core

The regular space is the little `C^u` space of supported functions, where
`t < u < r-1`. The classical product/composition estimate gives membership
and a norm bound for the literal function `g * f ∘ F`; it does not assume
an invariant analytic subspace or a spectral conclusion. Lifting this
function through its injective representation constructs a bounded regular
endomorphism. Smooth-core identities extend by density to its analytic and
physical realizations. Pointwise averaging then preserves both identities.

This replaces an unjustified regularity upgrade of bounded observables
under noise with merely bounded density. Normalized powers of an actual
regular seed stay in the regular core, with no smoothing assumption.
The law may vary with the noise intensity.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Topology

namespace LeanShared.InvariantFiniteRegularTransfer

open FiniteRegularTransferRealization

variable {X Ω R : Type*} [NormedAddCommGroup R] [NormedSpace ℂ R]
  (view : R →ₗ[ℂ] (X → ℂ)) (hview : Function.Injective view)
  (F : Ω → X → X) (g : X → ℝ)
  (hregular : ∀ a f, weightedComposition (F a) g (view f) ∈ view.range)

/-- The literal weighted composition on the invariant regular space. -/
def action (a : Ω) : R →ₗ[ℂ] R := regularAction view R view hview F g hregular a

@[simp] theorem action_apply (a : Ω) (f : R) (x : X) :
    view (action view hview F g hregular a f) x = (g x : ℂ) * view f (F a x) :=
  regularAction_apply view R view hview F g hregular a f x

variable (C : ℝ)
  (hbound : ∀ a f, ‖action view hview F g hregular a f‖ ≤ C * ‖f‖)

/-- Ordinary finite-Hölder product/composition bounds construct the regular
operator; completed anisotropic invariance is not an input. -/
def operator (a : Ω) : R →L[ℂ] R :=
  (action view hview F g hregular a).mkContinuous C (hbound a)

@[simp] theorem operator_apply (a : Ω) (f : R) :
    operator view hview F g hregular C hbound a f = action view hview F g hregular a f := rfl

theorem operator_norm_le (hC : 0 ≤ C) (a : Ω) :
    ‖operator view hview F g hregular C hbound a‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

/-- Actual function agreement holds for every finite-regular input. -/
theorem operator_function (a : Ω) (f : R) (x : X) :
    view (operator view hview F g hregular C hbound a f) x =
      (g x : ℂ) * view f (F a x) := action_apply view hview F g hregular a f x

variable {Core B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
  (smooth : Core → R) (dense : DenseRange smooth)
  (realize : R →L[ℂ] B) (P : Ω → B →L[ℂ] B)

include dense in
/-- Agreement on literal smooth functions proves the whole regular-space
intertwining law for either the analytic or physical representation. -/
theorem intertwining (hcore : ∀ a c,
    realize (action view hview F g hregular a (smooth c)) = P a (realize (smooth c)))
    (a : Ω) :
    realize.comp (operator view hview F g hregular C hbound a) = (P a).comp realize := by
  apply ContinuousLinearMap.ext
  intro f
  refine dense.induction_on (p := fun f =>
    realize (operator view hview F g hregular C hbound a f) = P a (realize f)) f
    (isClosed_eq (realize.continuous.comp (operator view hview F g hregular C hbound a).continuous)
      ((P a).continuous.comp realize.continuous)) ?_
  intro c
  exact hcore a c

include dense in
/-- Core continuity and the actual uniform regular norm bound give
continuity on every regular input. -/
theorem continuous_orbit [TopologicalSpace Ω] (hC : 0 ≤ C)
    (hcontinuous : ∀ c, Continuous (fun a => action view hview F g hregular a (smooth c)))
    (f : R) : Continuous (fun a => operator view hview F g hregular C hbound a f) := by
  apply DenseCoreRandomOperators.continuous_of_denseRange _ C
    (operator_norm_le view hview F g hregular C hbound hC) smooth dense _ f
  exact hcontinuous

include dense in
theorem measurable_orbit [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [SecondCountableTopology Ω]
    (hcontinuous : ∀ c, Continuous (fun a => action view hview F g hregular a (smooth c)))
    (f : R) : StronglyMeasurable (fun a => operator view hview F g hregular C hbound a f) := by
  apply DenseCoreRandomOperators.stronglyMeasurable_of_continuous_core _ smooth dense _ f
  exact hcontinuous

section Average

variable [CompleteSpace R] [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (hmeas : ∀ f : R, AEStronglyMeasurable
    (fun a => operator view hview F g hregular C hbound a f) μ)
  (hC : 0 ≤ C)

/-- The varying-law construction is instantiated separately at each
intensity. Its outputs are actual regular functions. -/
def average : R →L[ℂ] R := AnnealedOperatorBounds.pointwiseAnnealed μ
  (operator view hview F g hregular C hbound) hmeas C
  (operator_norm_le view hview F g hregular C hbound hC)

omit [CompleteSpace R] in
@[simp] theorem average_apply (f : R) :
    average view hview F g hregular C hbound μ hmeas hC f =
      ∫ a, operator view hview F g hregular C hbound a f ∂μ := rfl

variable [CompleteSpace B]
  (hPmeas : ∀ b : B, AEStronglyMeasurable (fun a => P a b) μ)
  (CP : ℝ) (hPbound : ∀ a, ‖P a‖ ≤ CP)

include dense in
/-- The whole-space annealed compatibility is deduced from genuine
smooth-core agreement, not supplied as a target invariant-core hypothesis. -/
theorem average_intertwining (hcore : ∀ a c,
    realize (action view hview F g hregular a (smooth c)) = P a (realize (smooth c))) :
    realize.comp (average view hview F g hregular C hbound μ hmeas hC) =
      (AnnealedOperatorBounds.pointwiseAnnealed μ P hPmeas CP hPbound).comp realize := by
  apply AnnealedOperatorBounds.pointwiseAnnealed_compatibility μ
    (operator view hview F g hregular C hbound) hmeas C
    (operator_norm_le view hview F g hregular C hbound hC) P hPmeas CP hPbound realize
  intro a f
  exact congrArg (fun T : R →L[ℂ] B => T f)
    (intertwining view hview F g hregular C hbound smooth dense realize P hcore a)

end Average

end LeanShared.InvariantFiniteRegularTransfer
