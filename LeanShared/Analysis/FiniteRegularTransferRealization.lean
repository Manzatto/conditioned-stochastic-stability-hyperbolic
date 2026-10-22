module

public import LeanShared.Analysis.NormCompletionComparison
public import LeanShared.Analysis.DenseCoreRandomOperators
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Literal finite-regularity weighted transfer on the strong completion

For finite fractional `C^r` maps and `C^{r-1}` weights, weighted
composition of a smooth core function need not be smooth. The actual
pointwise product instead belongs to the classical finite-regularity
function space `R`, which is realized in the completed strong chart norm.
A cited anisotropic core norm bound then constructs the operator on that
completion. Neither a smooth-core endomorphism nor a supplied completed
operator is assumed.

The classical inputs are finite-regularity product/composition membership,
the anisotropic realization of these functions (with its literal integral
pairing), and continuous finite-regularity noisy core orbits. For fractional
regularity the last input uses uniform top Hölder bounds and interpolation
to a lower exponent; joint `C¹` alone must not be mistaken for continuity
in the highest `C^{r-1}` norm.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace LeanShared.FiniteRegularTransferRealization

open DyadicCompletion

variable {X Ω Core V : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- The literal weighted composition, as a function-valued linear map. -/
def weightedComposition (F : X → X) (g : X → ℝ) : (X → ℂ) →ₗ[ℂ] (X → ℂ) where
  toFun f x := (g x : ℂ) * f (F x)
  map_add' f h := by ext x; simp [mul_add]
  map_smul' a f := by ext x; simp [mul_left_comm]

variable (q : Core →ₗ[ℂ] V) (smooth : Core →ₗ[ℂ] (X → ℂ))
  (R : Type*) [NormedAddCommGroup R] [NormedSpace ℂ R]
  (view : R →ₗ[ℂ] (X → ℂ)) (hview : Function.Injective view)
  (realize : R →L[ℂ] closedCore q)
  (F : Ω → X → X) (g : X → ℝ)
  (hregular : ∀ a c, weightedComposition (F a) g (smooth c) ∈ view.range)

/-- Its target is the finite-regularity space, rather than the smooth core. -/
def regularAction (a : Ω) : Core →ₗ[ℂ] R :=
  (LinearEquiv.ofInjective view hview).symm.toLinearMap.comp
    (((weightedComposition (F a) g).comp smooth).codRestrict view.range (hregular a))

@[simp] theorem regularAction_apply (a : Ω) (c : Core) (x : X) :
    view (regularAction smooth R view hview F g hregular a c) x = (g x : ℂ) * smooth c (F a x) := by
  have hv := LinearEquiv.ofInjective_symm_apply (f := view)
    (h := hview) ⟨weightedComposition (F a) g (smooth c), hregular a c⟩
  exact congrFun hv x

def targetCore (a : Ω) : Core →ₗ[ℂ] closedCore q :=
  realize.toLinearMap.comp (regularAction smooth R view hview F g hregular a)

/-- Extension from the smooth input core into the actual strong completion. -/
def operator (a : Ω) : closedCore q →L[ℂ] closedCore q :=
  (targetCore q smooth R view hview realize F g hregular a).extendOfNorm (coreLift q)

variable (L : ℝ)
  (hbound : ∀ a c, ‖targetCore q smooth R view hview realize F g hregular a c‖ ≤ L * ‖q c‖)

include hbound in
@[simp] theorem operator_core (a : Ω) (c : Core) :
    operator q smooth R view hview realize F g hregular a (coreLift q c) =
      realize (regularAction smooth R view hview F g hregular a c) :=
  LinearMap.extendOfNorm_eq (f := targetCore q smooth R view hview realize F g hregular a)
    (e := coreLift q) (coreLift_dense q) ⟨L, hbound a⟩ c

include hbound in
theorem operator_norm_le (hL : 0 ≤ L) (a : Ω) :
    ‖operator q smooth R view hview realize F g hregular a‖ ≤ L :=
  LinearMap.opNorm_extendOfNorm_le (coreLift_dense q) hL (hbound a)

include hbound in
/-- Exact pointwise multiplication/composition agreement in distribution
pairing, including finite-regularity output functions. -/
theorem operator_core_pairing [MeasurableSpace X] (μ : Measure X) (test : X → ℂ)
    (pairing : closedCore q →L[ℂ] ℂ)
    (hpairing : ∀ f : R, pairing (realize f) = ∫ x, view f x * test x ∂μ)
    (a : Ω) (c : Core) :
    pairing (operator q smooth R view hview realize F g hregular a (coreLift q c)) =
      ∫ x, ((g x : ℂ) * smooth c (F a x)) * test x ∂μ := by
  rw [operator_core q smooth R view hview realize F g hregular L hbound, hpairing]
  simp only [regularAction_apply]

include hbound in
theorem continuous_core_orbit [TopologicalSpace Ω]
    (horbit : ∀ c, Continuous (fun a => regularAction smooth R view hview F g hregular a c)) (c : Core) :
    Continuous (fun a => operator q smooth R view hview realize F g hregular a (coreLift q c)) := by
  have h := realize.continuous.comp (horbit c)
  exact h.congr (fun a => (operator_core q smooth R view hview realize F g hregular L hbound a c).symm)

include hbound in
theorem continuous_operator_orbit [TopologicalSpace Ω] (hL : 0 ≤ L)
    (horbit : ∀ c, Continuous (fun a => regularAction smooth R view hview F g hregular a c))
    (x : closedCore q) :
    Continuous (fun a => operator q smooth R view hview realize F g hregular a x) :=
  DenseCoreRandomOperators.continuous_of_denseRange _ L
    (operator_norm_le q smooth R view hview realize F g hregular L hbound hL)
    (coreLift q) (coreLift_dense q)
    (continuous_core_orbit q smooth R view hview realize F g hregular L hbound horbit) x

include hbound in
theorem measurable_operator_orbit [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [SecondCountableTopology Ω]
    (horbit : ∀ c, Continuous (fun a => regularAction smooth R view hview F g hregular a c))
    (x : closedCore q) :
    StronglyMeasurable (fun a => operator q smooth R view hview realize F g hregular a x) :=
  DenseCoreRandomOperators.stronglyMeasurable_of_continuous_core _ (coreLift q) (coreLift_dense q)
    (continuous_core_orbit q smooth R view hview realize F g hregular L hbound horbit) x

end LeanShared.FiniteRegularTransferRealization
