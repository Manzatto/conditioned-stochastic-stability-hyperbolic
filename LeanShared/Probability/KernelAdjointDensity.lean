module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# A kernel left eigenmeasure gives an adjoint right eigenfunction

Actual nonnegative kernel duality transports density-weighted measures.
Uniqueness of densities then derives the adjoint harmonic equation almost
everywhere. Continuity on the actual reference-measure support upgrades
this to a pointwise equation, without a continuous ambient extension.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace LeanShared.KernelAdjointDensity

variable {X : Type*} [MeasurableSpace X]

/-- Bilinear duality of the actual kernel integrals, for all nonnegative
measurable tests. This can be produced by per-noise change of variables. -/
def IsAdjoint (K L : Kernel X X) (σ : Measure X) : Prop :=
  ∀ (f h : X → ℝ≥0∞), Measurable f → Measurable h →
    (∫⁻ x, h x * (∫⁻ y, f y ∂L x) ∂σ) =
      ∫⁻ x, f x * (∫⁻ y, h y ∂K x) ∂σ

/-- The left action of the kernel on a density-weighted reference measure
is exactly the reference measure weighted by the adjoint kernel integral. -/
theorem comp_withDensity (K L : Kernel X X) (σ : Measure X) (hdual : IsAdjoint K L σ)
    (m : X → ℝ≥0∞) (hm : Measurable m) :
    K ∘ₘ σ.withDensity m = σ.withDensity (fun x => ∫⁻ y, m y ∂L x) := by
  have hLm : Measurable (fun x => ∫⁻ y, m y ∂L x) :=
    (Measure.measurable_lintegral hm).comp L.measurable
  apply Measure.ext_of_lintegral
  intro h hh
  have hKh : Measurable (fun x => ∫⁻ y, h y ∂K x) :=
    (Measure.measurable_lintegral hh).comp K.measurable
  rw [Measure.lintegral_bind K.aemeasurable hh.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul σ hm hKh,
    lintegral_withDensity_eq_lintegral_mul σ hLm hh]
  simpa only [Pi.mul_apply, mul_comm] using (hdual m h hm hh).symm

/-- The adjoint harmonic density equation is derived from the actual left
measure equation by uniqueness of densities over a sigma-finite reference. -/
theorem density_eigen_ae (K L : Kernel X X) (σ : Measure X) [SigmaFinite σ]
    (hdual : IsAdjoint K L σ) (m : X → ℝ≥0∞) (hm : Measurable m) (r : ℝ≥0∞)
    (hleft : K ∘ₘ σ.withDensity m = r • σ.withDensity m) :
    (fun x => ∫⁻ y, m y ∂L x) =ᵐ[σ] (fun x => r * m x) := by
  have hLm : Measurable (fun x => ∫⁻ y, m y ∂L x) :=
    (Measure.measurable_lintegral hm).comp L.measurable
  apply (withDensity_eq_iff_of_sigmaFinite hLm.aemeasurable
    (measurable_const.mul hm).aemeasurable).mp
  rw [← comp_withDensity K L σ hdual m hm]
  change K ∘ₘ σ.withDensity m = σ.withDensity (r • m)
  rw [withDensity_smul r hm, hleft]

/-- Finite density mass is an alternative to sigma-finiteness of the
reference measure for uniqueness of the harmonic density. -/
theorem density_eigen_ae_of_finite_mass (K L : Kernel X X) (σ : Measure X)
    (hdual : IsAdjoint K L σ) (m : X → ℝ≥0∞) (hm : Measurable m) (r : ℝ≥0∞)
    (hleft : K ∘ₘ σ.withDensity m = r • σ.withDensity m)
    (hmass : ∫⁻ x, r * m x ∂σ ≠ ∞) :
    (fun x => ∫⁻ y, m y ∂L x) =ᵐ[σ] (fun x => r * m x) := by
  have hLm : Measurable (fun x => ∫⁻ y, m y ∂L x) :=
    (Measure.measurable_lintegral hm).comp L.measurable
  apply Filter.EventuallyEq.symm
  apply (withDensity_eq_iff (measurable_const.mul hm).aemeasurable hLm.aemeasurable hmass).mp
  change σ.withDensity (r • m) = _
  rw [withDensity_smul r hm, ← hleft, comp_withDensity K L σ hdual m hm]

section Support

variable [TopologicalSpace X]

/-- Continuity is needed only on a closed conull set containing the actual
support. This works at boundary points and requires no ambient extension. -/
theorem eqOn_support_of_ae_eq_on_closed {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (σ : Measure X) (S : Set X) (hS : IsClosed S) (hconull : S ∈ ae σ)
    (f g : X → Y) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hae : f =ᵐ[σ] g) : EqOn f g σ.support := by
  have heq : {x ∈ S | f x = g x} ∈ ae σ := by
    filter_upwards [hconull, hae] with x hx he
    exact ⟨hx, he⟩
  intro x hx
  exact (Measure.support_subset_of_isClosed (hS.isClosed_eq hf hg) heq hx).2

/-- In particular, regularity makes the actual support conull. -/
theorem eqOn_support_of_ae_eq {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (σ : Measure X) [σ.Regular] (f g : X → Y)
    (hf : ContinuousOn f σ.support) (hg : ContinuousOn g σ.support)
    (hae : f =ᵐ[σ] g) : EqOn f g σ.support :=
  eqOn_support_of_ae_eq_on_closed σ σ.support Measure.isClosed_support
    Measure.support_mem_ae_of_regular f g hf hg hae

/-- The derived ENNReal harmonic law holds at every actual support point
when the density and its adjoint image are continuous there. -/
theorem density_eigen_on_support (K L : Kernel X X) (σ : Measure X) [SigmaFinite σ]
    [σ.Regular] (hdual : IsAdjoint K L σ) (m : X → ℝ≥0∞) (hm : Measurable m)
    (r : ℝ≥0∞) (hr : r ≠ ∞)
    (hleft : K ∘ₘ σ.withDensity m = r • σ.withDensity m)
    (hmc : ContinuousOn m σ.support)
    (hLmc : ContinuousOn (fun x => ∫⁻ y, m y ∂L x) σ.support) :
    ∀ x ∈ σ.support, (∫⁻ y, m y ∂L x) = r * m x :=
  eqOn_support_of_ae_eq σ _ _ hLmc
    ((ENNReal.continuous_const_mul hr).comp_continuousOn hmc)
    (density_eigen_ae K L σ hdual m hm r hleft)

end Support

section RealDensity

/-- For real nonnegative densities, pointwise Bochner integrability is
enough to convert the derived ENNReal equation to the real harmonic law. -/
theorem real_density_eigen_ae (K L : Kernel X X) (σ : Measure X) [SigmaFinite σ]
    (hdual : IsAdjoint K L σ) (m : X → ℝ) (hm : Measurable m) (hm0 : ∀ x, 0 ≤ m x)
    (r : ℝ) (hr : 0 ≤ r)
    (hleft : K ∘ₘ σ.withDensity (fun x => ENNReal.ofReal (m x)) =
      ENNReal.ofReal r • σ.withDensity (fun x => ENNReal.ofReal (m x)))
    (hint : ∀ᵐ x ∂σ, Integrable m (L x)) :
    (fun x => ∫ y, m y ∂L x) =ᵐ[σ] (fun x => r * m x) := by
  have he := density_eigen_ae K L σ hdual _ hm.ennreal_ofReal (ENNReal.ofReal r) hleft
  filter_upwards [he, hint] with x hx hi
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hm0),
    ← ENNReal.ofReal_mul hr] at hx
  have ht := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hm0),
    ENNReal.toReal_ofReal (mul_nonneg hr (hm0 x))] using ht

variable [TopologicalSpace X]

/-- Real continuity only on the reference support suffices for the exact
pointwise inverse harmonic law. Its almost-everywhere equation is derived. -/
theorem real_density_eigen_on_support (K L : Kernel X X) (σ : Measure X) [SigmaFinite σ]
    [σ.Regular] (hdual : IsAdjoint K L σ) (m : X → ℝ) (hm : Measurable m)
    (hm0 : ∀ x, 0 ≤ m x) (r : ℝ) (hr : 0 ≤ r)
    (hleft : K ∘ₘ σ.withDensity (fun x => ENNReal.ofReal (m x)) =
      ENNReal.ofReal r • σ.withDensity (fun x => ENNReal.ofReal (m x)))
    (hint : ∀ᵐ x ∂σ, Integrable m (L x))
    (hmc : ContinuousOn m σ.support)
    (hLmc : ContinuousOn (fun x => ∫ y, m y ∂L x) σ.support) :
    ∀ x ∈ σ.support, (∫ y, m y ∂L x) = r * m x :=
  eqOn_support_of_ae_eq σ _ _ hLmc (continuousOn_const.mul hmc)
    (real_density_eigen_ae K L σ hdual m hm hm0 r hr hleft hint)

/-- A closed survival set identified with the actual reference support
requires continuity only on that set, including its boundary. -/
theorem real_density_eigen_on_set (K L : Kernel X X) (σ : Measure X) [SigmaFinite σ]
    [σ.Regular] (hdual : IsAdjoint K L σ) (S : Set X) (hsupport : σ.support = S)
    (m : X → ℝ) (hm : Measurable m) (hm0 : ∀ x, 0 ≤ m x) (r : ℝ) (hr : 0 ≤ r)
    (hleft : K ∘ₘ σ.withDensity (fun x => ENNReal.ofReal (m x)) =
      ENNReal.ofReal r • σ.withDensity (fun x => ENNReal.ofReal (m x)))
    (hint : ∀ᵐ x ∂σ, Integrable m (L x)) (hmc : ContinuousOn m S)
    (hLmc : ContinuousOn (fun x => ∫ y, m y ∂L x) S) :
    ∀ x ∈ S, (∫ y, m y ∂L x) = r * m x := by
  rw [← hsupport] at hmc hLmc ⊢
  exact real_density_eigen_on_support K L σ hdual m hm hm0 r hr hleft hint hmc hLmc

variable [OpensMeasurableSpace X]

/-- For an actual kernel killed on a compact reference-support set,
continuity on that set supplies all Bochner integrability. No continuity
or boundedness of the ambient density outside the set is required. -/
theorem real_density_eigen_on_compact [T2Space X]
    (K L : Kernel X X) [IsFiniteKernel L] (σ : Measure X) [SigmaFinite σ] [σ.Regular]
    (hdual : IsAdjoint K L σ) (S : Set X) (hS : IsCompact S) (hsupport : σ.support = S)
    (hLS : ∀ x ∈ S, (L x).restrict S = L x)
    (m : X → ℝ) (hm : Measurable m) (hm0 : ∀ x, 0 ≤ m x) (r : ℝ) (hr : 0 ≤ r)
    (hleft : K ∘ₘ σ.withDensity (fun x => ENNReal.ofReal (m x)) =
      ENNReal.ofReal r • σ.withDensity (fun x => ENNReal.ofReal (m x)))
    (hmc : ContinuousOn m S) (hLmc : ContinuousOn (fun x => ∫ y, m y ∂L x) S) :
    ∀ x ∈ S, (∫ y, m y ∂L x) = r * m x := by
  apply real_density_eigen_on_set K L σ hdual S hsupport m hm hm0 r hr hleft _ hmc hLmc
  filter_upwards [Measure.support_mem_ae_of_regular (μ := σ)] with x hx
  have hi : Integrable m ((L x).restrict S) := hmc.integrableOn_compact hS
  rwa [hLS x (hsupport ▸ hx)] at hi

/-- For a bounded continuous density and an actual finite adjoint kernel,
Bochner integrability is automatic; only continuity of its actual image
on the reference support remains a regularity input. -/
theorem bounded_density_eigen_on_support (K L : Kernel X X) [IsFiniteKernel L]
    (σ : Measure X) [SigmaFinite σ] [σ.Regular] (hdual : IsAdjoint K L σ)
    (m : X →ᵇ ℝ) (hm0 : ∀ x, 0 ≤ m x) (r : ℝ) (hr : 0 ≤ r)
    (hleft : K ∘ₘ σ.withDensity (fun x => ENNReal.ofReal (m x)) =
      ENNReal.ofReal r • σ.withDensity (fun x => ENNReal.ofReal (m x)))
    (hLmc : ContinuousOn (fun x => ∫ y, m y ∂L x) σ.support) :
    ∀ x ∈ σ.support, (∫ y, m y ∂L x) = r * m x :=
  real_density_eigen_on_support K L σ hdual m m.continuous.measurable hm0 r hr hleft
    (ae_of_all σ fun x => m.integrable (L x)) m.continuous.continuousOn hLmc

/-- On an open-positive reference space, global continuity yields the
pointwise real harmonic equation without a separate regularity assumption. -/
theorem bounded_density_eigen_of_full_support (K L : Kernel X X) [IsFiniteKernel L]
    (σ : Measure X) [SigmaFinite σ] [σ.IsOpenPosMeasure] (hdual : IsAdjoint K L σ)
    (m : X →ᵇ ℝ) (hm0 : ∀ x, 0 ≤ m x) (r : ℝ) (hr : 0 ≤ r)
    (hleft : K ∘ₘ σ.withDensity (fun x => ENNReal.ofReal (m x)) =
      ENNReal.ofReal r • σ.withDensity (fun x => ENNReal.ofReal (m x)))
    (hLmc : Continuous (fun x => ∫ y, m y ∂L x)) :
    ∀ x, (∫ y, m y ∂L x) = r * m x := by
  have he := real_density_eigen_ae K L σ hdual m m.continuous.measurable hm0 r hr hleft
    (ae_of_all σ fun x => m.integrable (L x))
  exact congrFun (Measure.eq_of_ae_eq he hLmc (continuous_const.mul m.continuous))

end RealDensity

end LeanShared.KernelAdjointDensity
