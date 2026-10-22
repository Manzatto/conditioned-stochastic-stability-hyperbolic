module

public import ConditionedStochasticStabilityHyperbolic.Spectral.StrongFeller
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Ring

/-!
# Actual complex transfer and subtype-to-ambient smoothing

Real strong-Feller regularity supplies the real and imaginary parts of every
bounded measurable RCLike integral. The resulting genuine bounded continuous
operators are complex-linear when the scalar is complex. Subtype extension
here is measurable zero extension followed by one kernel step, with no claim
that zero extension itself is continuous.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.ComplexStrongFeller

variable {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]

def zeroExtend (U : Set X) (f : U → 𝕜) : X → 𝕜 :=
  Function.extend Subtype.val f (fun _ => 0)

omit [MeasurableSpace X] in
@[simp] theorem zeroExtend_coe (U : Set X) (f : U → 𝕜) (x : U) :
    zeroExtend U f x.val = f x := Subtype.val_injective.extend_apply _ _ _

omit [MeasurableSpace X] in
theorem zeroExtend_of_not_mem (U : Set X) (f : U → 𝕜) (x : X) (hx : x ∉ U) :
    zeroExtend U f x = 0 := by
  apply Function.extend_apply'
  rintro ⟨u, rfl⟩
  exact hx u.property

theorem measurable_zeroExtend (U : Set X) (hU : MeasurableSet U)
    (f : U → 𝕜) (hf : Measurable f) : Measurable (zeroExtend U f) :=
  (MeasurableEmbedding.subtype_coe hU).measurable_extend hf measurable_const

omit [MeasurableSpace X] in
theorem norm_zeroExtend_le (U : Set X) (f : U → 𝕜) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ u, ‖f u‖ ≤ B) (x : X) : ‖zeroExtend U f x‖ ≤ B := by
  by_cases hx : x ∈ U
  · rw [zeroExtend_coe U f ⟨x, hx⟩]
    exact hf ⟨x, hx⟩
  · rw [zeroExtend_of_not_mem U f x hx, norm_zero]
    exact hB

omit [MeasurableSpace X] in
theorem zeroExtend_add (U : Set X) (f g : U → 𝕜) :
    zeroExtend U (f + g) = zeroExtend U f + zeroExtend U g := by
  funext x
  by_cases hx : x ∈ U
  · change zeroExtend U (f + g) x = zeroExtend U f x + zeroExtend U g x
    rw [zeroExtend_coe U (f + g) ⟨x, hx⟩,
      zeroExtend_coe U f ⟨x, hx⟩, zeroExtend_coe U g ⟨x, hx⟩]
    rfl
  · simp [zeroExtend_of_not_mem U _ x hx]

omit [MeasurableSpace X] in
theorem zeroExtend_smul (U : Set X) (a : 𝕜) (f : U → 𝕜) :
    zeroExtend U (a • f) = a • zeroExtend U f := by
  funext x
  by_cases hx : x ∈ U
  · change zeroExtend U (a • f) x = a • zeroExtend U f x
    rw [zeroExtend_coe U (a • f) ⟨x, hx⟩, zeroExtend_coe U f ⟨x, hx⟩]
    rfl
  · simp [zeroExtend_of_not_mem U _ x hx]

variable [TopologicalSpace X] [OpensMeasurableSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)

local instance killedKernelFinite : IsFiniteKernel C.killedTransition := by
  change IsFiniteKernel C.toKilledKernel.kernel
  infer_instance

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
theorem bounded_integrable (f : X → 𝕜) (hf : Measurable f) {B : ℝ}
    (hb : ∀ y, ‖f y‖ ≤ B) (x : X) : Integrable f (C.killedTransition x) :=
  Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ hb)

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
theorem integral_norm_le (f : X → 𝕜) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ y, ‖f y‖ ≤ B) (x : X) : ‖∫ y, f y ∂C.killedTransition x‖ ≤ B := by
  calc
    _ ≤ B * (C.killedTransition x).real univ :=
      norm_integral_le_of_norm_le_const (ae_of_all _ hb)
    _ ≤ B := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (StrongFeller.killedTransition_real_mass_le_one C x) hB

omit [OpensMeasurableSpace X] in
include hSF in
theorem continuous_integral (f : X → 𝕜) (hf : Measurable f) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ y, ‖f y‖ ≤ B) :
    Continuous (fun x => ∫ y, f y ∂C.killedTransition x) := by
  have hr := hSF (fun y => RCLike.re (f y)) (RCLike.continuous_re.measurable.comp hf)
    ⟨B, hB, fun y => (RCLike.abs_re_le_norm _).trans (hb y)⟩
  have hi := hSF (fun y => RCLike.im (f y)) (RCLike.continuous_im.measurable.comp hf)
    ⟨B, hB, fun y => (RCLike.abs_im_le_norm _).trans (hb y)⟩
  have he : (fun x => ∫ y, f y ∂C.killedTransition x) =
      (fun x => ((∫ y, RCLike.re (f y) ∂C.killedTransition x : ℝ) : 𝕜) +
        ((∫ y, RCLike.im (f y) ∂C.killedTransition x : ℝ) : 𝕜) * RCLike.I) := by
    funext x
    exact (integral_re_add_im (bounded_integrable C f hf hb x)).symm
  rw [he]
  exact (RCLike.continuous_ofReal.comp hr).add
    ((RCLike.continuous_ofReal.comp hi).mul continuous_const)

def integralFunction (f : X → 𝕜) (hf : Measurable f) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ y, ‖f y‖ ≤ B) : X →ᵇ 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => ∫ y, f y ∂C.killedTransition x)
    (continuous_integral C hSF f hf hB hb) B (integral_norm_le C f hB hb)

def transferLinearMap : (X →ᵇ 𝕜) →ₗ[𝕜] (X →ᵇ 𝕜) where
  toFun f := integralFunction C hSF f f.continuous.measurable (norm_nonneg f) f.norm_coe_le_norm
  map_add' f g := by
    ext x
    exact integral_add (bounded_integrable C f f.continuous.measurable f.norm_coe_le_norm x)
      (bounded_integrable C g g.continuous.measurable g.norm_coe_le_norm x)
  map_smul' a f := by
    ext x
    change (∫ y, a • f y ∂C.killedTransition x) = a • ∫ y, f y ∂C.killedTransition x
    exact integral_smul a (fun y => f y)

def transferOperator : (X →ᵇ 𝕜) →L[𝕜] (X →ᵇ 𝕜) :=
  (transferLinearMap C hSF).mkContinuous 1 (fun f => by
    rw [one_mul]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    exact integral_norm_le C f (norm_nonneg f) f.norm_coe_le_norm)

theorem transferOperator_apply (f : X →ᵇ 𝕜) (x : X) :
    transferOperator C hSF f x = ∫ y, f y ∂C.killedTransition x := rfl

theorem norm_transferOperator_le_one : ‖transferOperator (𝕜 := 𝕜) C hSF‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

variable (U : Set X) (hU : MeasurableSet U)

def extensionLinearMap : (U →ᵇ 𝕜) →ₗ[𝕜] (X →ᵇ 𝕜) where
  toFun f := integralFunction C hSF (zeroExtend U f)
    (measurable_zeroExtend U hU f f.continuous.measurable) (norm_nonneg f)
    (norm_zeroExtend_le U f (norm_nonneg f) f.norm_coe_le_norm)
  map_add' f g := by
    ext x
    change (∫ y, zeroExtend U ((f : U → 𝕜) + (g : U → 𝕜)) y ∂C.killedTransition x) =
      (∫ y, zeroExtend U f y ∂C.killedTransition x) +
        ∫ y, zeroExtend U g y ∂C.killedTransition x
    rw [zeroExtend_add]
    exact integral_add
      (bounded_integrable C (zeroExtend U f)
        (measurable_zeroExtend U hU f f.continuous.measurable)
        (norm_zeroExtend_le U f (norm_nonneg f) f.norm_coe_le_norm) x)
      (bounded_integrable C (zeroExtend U g)
        (measurable_zeroExtend U hU g g.continuous.measurable)
        (norm_zeroExtend_le U g (norm_nonneg g) g.norm_coe_le_norm) x)
  map_smul' a f := by
    ext x
    change (∫ y, zeroExtend U (a • (f : U → 𝕜)) y ∂C.killedTransition x) =
      a • ∫ y, zeroExtend U f y ∂C.killedTransition x
    rw [zeroExtend_smul]
    exact integral_smul a (zeroExtend U f)

/-- Actual subtype-to-ambient smoothing, bounded by one kernel step. -/
def extensionOperator : (U →ᵇ 𝕜) →L[𝕜] (X →ᵇ 𝕜) :=
  (extensionLinearMap C hSF U hU).mkContinuous 1 (fun f => by
    rw [one_mul]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    exact integral_norm_le C (zeroExtend U f) (norm_nonneg f)
      (norm_zeroExtend_le U f (norm_nonneg f) f.norm_coe_le_norm))

theorem extensionOperator_apply (f : U →ᵇ 𝕜) (x : X) :
    extensionOperator C hSF U hU f x = ∫ y, zeroExtend U f y ∂C.killedTransition x := rfl

theorem extensionOperator_apply_subtype (f : U →ᵇ 𝕜) (x : X) :
    extensionOperator C hSF U hU f x = ∫ y : U, f y ∂(C.killedTransition x).comap Subtype.val := by
  rw [extensionOperator_apply]
  have hind : U.indicator (zeroExtend U f) = zeroExtend U f := by
    funext y
    by_cases hy : y ∈ U
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy, zeroExtend_of_not_mem U f y hy]
  calc
    _ = ∫ y in U, zeroExtend U f y ∂C.killedTransition x := by
      rw [← integral_indicator hU, hind]
    _ = ∫ y : U, zeroExtend U f y.val ∂(C.killedTransition x).comap Subtype.val :=
      (integral_subtype_comap hU (zeroExtend U f)).symm
    _ = _ := by simp only [zeroExtend_coe]

theorem norm_extensionOperator_le_one : ‖extensionOperator (𝕜 := 𝕜) C hSF U hU‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end ConditionedStochasticStabilityHyperbolic.ComplexStrongFeller
