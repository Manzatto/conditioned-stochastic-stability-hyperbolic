module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Actual finite-word averaging for random bounded operators

A pointwise a.e. strongly measurable, uniformly bounded family of complex
operators defines a genuine bounded annealed operator. Its evaluated powers
are integrals of actual composed operators on finite independent noise
products, without separability of the whole operator or vector space.
Uniform deterministic word estimates give annealed power estimates and the
one-step strong-to-weak perturbation estimate by actual probability averaging.

A separate, stronger operator-norm Bochner formulation is provided when that
extra integrability is known. It is not required by the pointwise producers.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace LeanShared.AnnealedOperatorBounds

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Finite independent noise samples, represented by recursive products. -/
def NoiseWords (Ω : Type u) : ℕ → Type u
  | 0 => PUnit.{u + 1}
  | n + 1 => Ω × NoiseWords Ω n

instance noiseWordsMeasurableSpace (n : ℕ) : MeasurableSpace (NoiseWords Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSpace PUnit.{u + 1})
  | succ n ih =>
      let : MeasurableSpace (NoiseWords Ω n) := ih
      exact inferInstanceAs (MeasurableSpace (Ω × NoiseWords Ω n))

/-- The actual finite product law of independent copies of the noise. -/
def wordMeasure (μ : Measure Ω) : (n : ℕ) → Measure (NoiseWords Ω n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => μ.prod (wordMeasure μ n)

instance wordMeasure_probability (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (wordMeasure μ n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ n ih =>
      change IsProbabilityMeasure (μ.prod (wordMeasure μ n))
      let : IsProbabilityMeasure (wordMeasure μ n) := ih
      infer_instance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The newest noise coordinate acts last on the vector:
`word (n+1) (ω,w) = A ω ∘ word n w`. -/
def operatorWord (A : Ω → E →L[ℂ] E) : (n : ℕ) → NoiseWords Ω n → E →L[ℂ] E
  | 0, _ => 1
  | n + 1, p => (A p.1).comp (operatorWord A n p.2)

/-- The actual Bochner average of the random operator. -/
def annealed (μ : Measure Ω) (A : Ω → E →L[ℂ] E) : E →L[ℂ] E := ∫ ω, A ω ∂μ

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → E →L[ℂ] E)
  (hA : Integrable A μ)

include hA

omit [CompleteSpace E] in
/-- All finite noise words are integrable in operator norm, derived from
one-step Bochner integrability and the product composition bound. -/
theorem operatorWord_integrable (n : ℕ) :
    Integrable (operatorWord A n) (wordMeasure μ n) := by
  induction n with
  | zero => exact integrable_const 1
  | succ n ih =>
      change Integrable (fun p : Ω × NoiseWords Ω n =>
        (A p.1).comp (operatorWord A n p.2)) (μ.prod (wordMeasure μ n))
      exact hA.op_fst_snd (op := fun f g => f.comp g) (by fun_prop)
        ⟨1, fun f g => by simpa only [one_mul] using ContinuousLinearMap.opNorm_comp_le f g⟩ ih

/-- Powers of the averaged operator are the actual independent noise-word
integrals, with composition order fixed by `operatorWord`. -/
theorem annealed_pow_eq_word_integral (n : ℕ) :
    annealed μ A ^ n = ∫ w, operatorWord A n w ∂wordMeasure μ n := by
  induction n with
  | zero =>
      change (1 : E →L[ℂ] E) = ∫ _w : NoiseWords Ω 0, (1 : E →L[ℂ] E) ∂wordMeasure μ 0
      simp
  | succ n ih =>
      rw [pow_succ', ih]
      exact (integral_prod_bilin (ContinuousLinearMap.compL ℂ E E E) hA
        (operatorWord_integrable μ A hA n)).symm

/-- Evaluation commutes with the checked finite-word average. -/
theorem annealed_pow_apply_eq_word_integral (n : ℕ) (x : E) :
    (annealed μ A ^ n) x = ∫ w, operatorWord A n w x ∂wordMeasure μ n := by
  rw [annealed_pow_eq_word_integral μ A hA n]
  exact ContinuousLinearMap.integral_apply (operatorWord_integrable μ A hA n) x

/-- A uniform deterministic word bound yields the annealed operator bound. -/
theorem norm_annealed_pow_le (n : ℕ) (B : ℝ)
    (hword : ∀ w, ‖operatorWord A n w‖ ≤ B) : ‖annealed μ A ^ n‖ ≤ B := by
  rw [annealed_pow_eq_word_integral μ A hA n]
  simpa using norm_integral_le_of_norm_le_const (ae_of_all (wordMeasure μ n) hword)

/-- A vector-dependent deterministic word bound is retained under averaging.
This is the form needed for two-norm Lasota--Yorke estimates. -/
theorem norm_annealed_pow_apply_le (n : ℕ) (x : E) (B : ℝ)
    (hword : ∀ w, ‖operatorWord A n w x‖ ≤ B) : ‖(annealed μ A ^ n) x‖ ≤ B := by
  rw [annealed_pow_apply_eq_word_integral μ A hA n x]
  simpa using norm_integral_le_of_norm_le_const (ae_of_all (wordMeasure μ n) hword)

/-- The weak growth estimate is derived from uniform deterministic words. -/
theorem annealed_geometric_power_bound (C C₀ : ℝ)
    (hword : ∀ n w, ‖operatorWord A n w‖ ≤ C * C₀ ^ n) :
    ∀ n, ‖annealed μ A ^ n‖ ≤ C * C₀ ^ n :=
  fun n => norm_annealed_pow_le μ A hA n _ (hword n)

/-- The strong Lasota--Yorke estimate is derived by actual averaging of its
uniform deterministic word estimate, with the weak norm represented by `ι`. -/
theorem annealed_lasota_yorke
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ι : E →L[ℂ] F) (C ρ C₀ : ℝ)
    (hword : ∀ n w x, ‖operatorWord A n w x‖ ≤
      C * ρ ^ n * ‖x‖ + C * C₀ ^ n * ‖ι x‖) :
    ∀ n x, ‖(annealed μ A ^ n) x‖ ≤ C * ρ ^ n * ‖x‖ + C * C₀ ^ n * ‖ι x‖ :=
  fun n x => norm_annealed_pow_apply_le μ A hA n x _ (fun w => hword n w x)

section WeakRealization

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [IsProbabilityMeasure μ] in
/-- Applying a strong-to-weak map after averaging is the actual average of
the strong-to-weak random operators. -/
theorem annealed_comp_left (ι : E →L[ℂ] F) :
    ι.comp (annealed μ A) = ∫ ω, ι.comp (A ω) ∂μ :=
  ((ContinuousLinearMap.compL ℂ E E F ι).integral_comp_comm hA).symm

omit [IsProbabilityMeasure μ] in
/-- Compatible one-step realizations on strong and weak spaces remain
compatible after actual averaging. -/
theorem annealed_compatibility (B : Ω → F →L[ℂ] F) (hB : Integrable B μ)
    (ι : E →L[ℂ] F) (hcompat : ∀ ω, ι.comp (A ω) = (B ω).comp ι) :
    ι.comp (annealed μ A) = (annealed μ B).comp ι := by
  rw [annealed_comp_left μ A hA ι]
  simp_rw [hcompat]
  exact (ContinuousLinearMap.compL ℂ E F F |>.flip ι).integral_comp_comm hB

omit hA [CompleteSpace E] in
/-- A uniform one-step perturbation estimate is retained by probability
averaging, with integrability explicit in the operator norm. -/
theorem norm_average_sub_le (R : Ω → E →L[ℂ] F) (hR : Integrable R μ)
    (R₀ : E →L[ℂ] F) (τ : ℝ) (hpert : ∀ ω, ‖R ω - R₀‖ ≤ τ) :
    ‖(∫ ω, R ω ∂μ) - R₀‖ ≤ τ := by
  have heq : (∫ ω, R ω - R₀ ∂μ) = (∫ ω, R ω ∂μ) - R₀ := by
    rw [integral_sub hR (integrable_const R₀)]
    simp
  rw [← heq]
  simpa using norm_integral_le_of_norm_le_const (ae_of_all μ hpert)

/-- The manuscript's one-step strong-to-weak perturbation bound follows
from the cited deterministic estimate by actual noise averaging. -/
theorem norm_annealed_weak_perturbation_le (ι : E →L[ℂ] F)
    (T : E →L[ℂ] E) (τ : ℝ)
    (hpert : ∀ ω, ‖ι.comp (A ω - T)‖ ≤ τ) :
    ‖ι.comp (annealed μ A - T)‖ ≤ τ := by
  have heq : ι.comp (annealed μ A - T) =
      (∫ ω, ι.comp (A ω) ∂μ) - ι.comp T := by
    rw [ContinuousLinearMap.comp_sub, annealed_comp_left μ A hA ι]
  rw [heq]
  apply norm_average_sub_le μ (fun ω => ι.comp (A ω))
    ((ContinuousLinearMap.compL ℂ E E F ι).integrable_comp hA) (ι.comp T) τ
  intro ω
  simpa only [ContinuousLinearMap.comp_sub] using hpert ω

end WeakRealization

section Pointwise

omit hA

variable (hmeas : ∀ x : E, AEStronglyMeasurable (fun ω => A ω x) μ)

omit [CompleteSpace E] [IsProbabilityMeasure μ] in
include hmeas in
/-- Pointwise measurable bounded linear maps can be applied to an
independent strongly measurable random vector. Simple-function approximation
requires no separability of the whole operator or vector space. -/
theorem aestronglyMeasurable_random_apply
    {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ) [SFinite ν]
    (f : Λ → E) (hf : AEStronglyMeasurable f ν) :
    AEStronglyMeasurable (fun p : Ω × Λ => A p.1 (f p.2)) (μ.prod ν) := by
  classical
  have hsimple (s : SimpleFunc Λ E) :
      AEStronglyMeasurable (fun p : Ω × Λ => A p.1 (s p.2)) (μ.prod ν) := by
    induction s using SimpleFunc.induction with
    | const c ht =>
        rename_i t
        have hbase : AEStronglyMeasurable (fun p : Ω × Λ => A p.1 c) (μ.prod ν) :=
          (hmeas c).comp_fst
        have h := hbase.indicator (ht.preimage measurable_snd)
        convert h using 1
        funext p
        by_cases hp : p.2 ∈ t
        · simp [hp, SimpleFunc.coe_piecewise]
        · simp [hp, SimpleFunc.coe_piecewise]
    | add _hs ihs iht =>
        convert ihs.add iht using 1
        funext p
        simp only [SimpleFunc.add_apply, map_add, Pi.add_apply]
  let s := hf.stronglyMeasurable_mk.approx
  apply aestronglyMeasurable_of_tendsto_ae Filter.atTop (fun n => hsimple (s n))
  have heq : ∀ᵐ p : Ω × Λ ∂μ.prod ν, f p.2 = hf.mk f p.2 :=
    hf.ae_eq_mk.comp_tendsto Measure.quasiMeasurePreserving_snd.tendsto_ae
  filter_upwards [heq] with p hp
  rw [hp]
  exact ((A p.1).continuous.tendsto _).comp (hf.stronglyMeasurable_mk.tendsto_approx p.2)

omit [CompleteSpace E] in
include hmeas in
/-- Actual finite word orbits are jointly a.e. strongly measurable,
derived from one-step pointwise measurability. -/
theorem operatorWord_apply_aestronglyMeasurable (n : ℕ) (x : E) :
    AEStronglyMeasurable (fun w => operatorWord A n w x) (wordMeasure μ n) := by
  induction n with
  | zero => exact aestronglyMeasurable_const
  | succ n ih =>
      exact aestronglyMeasurable_random_apply μ A hmeas (wordMeasure μ n)
        (fun w => operatorWord A n w x) ih

variable (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ ω, ‖A ω‖ ≤ M)

omit [CompleteSpace E] [MeasurableSpace Ω] in
include hM hbound in
/-- The uniform one-step operator bound controls each actual finite word. -/
theorem operatorWord_apply_bound (n : ℕ) (w : NoiseWords Ω n) (x : E) :
    ‖operatorWord A n w x‖ ≤ M ^ n * ‖x‖ := by
  induction n with
  | zero => simp [operatorWord]
  | succ n ih =>
      change ‖A w.1 (operatorWord A n w.2 x)‖ ≤ M ^ (n + 1) * ‖x‖
      calc
        _ ≤ ‖A w.1‖ * ‖operatorWord A n w.2 x‖ := (A w.1).le_opNorm _
        _ ≤ M * ‖operatorWord A n w.2 x‖ :=
          mul_le_mul_of_nonneg_right (hbound w.1) (norm_nonneg _)
        _ ≤ M * (M ^ n * ‖x‖) := mul_le_mul_of_nonneg_left (ih w.2) hM
        _ = M ^ (n + 1) * ‖x‖ := by rw [pow_succ']; exact (mul_assoc _ _ _).symm

omit [CompleteSpace E] in
include hmeas hM hbound in
/-- Pointwise finite-word Bochner integrability follows without any
operator-norm measurability assumption. -/
theorem operatorWord_apply_integrable (n : ℕ) (x : E) :
    Integrable (fun w => operatorWord A n w x) (wordMeasure μ n) :=
  Integrable.of_bound (operatorWord_apply_aestronglyMeasurable μ A hmeas n x)
    (M ^ n * ‖x‖) (ae_of_all _ (fun w => operatorWord_apply_bound A M hM hbound n w x))

omit [CompleteSpace E] hM in
include hmeas hbound in
theorem random_apply_integrable (x : E) : Integrable (fun ω => A ω x) μ := by
  apply Integrable.of_bound (hmeas x) (M * ‖x‖)
  exact ae_of_all _ fun ω => ((A ω).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hbound ω) (norm_nonneg x))

/-- The pointwise average is linear, proved from actual vector integrals. -/
def pointwiseAverageLinearMap : E →ₗ[ℂ] E where
  toFun x := ∫ ω, A ω x ∂μ
  map_add' x y := by
    simp only [map_add]
    exact integral_add (random_apply_integrable μ A hmeas M hbound x)
      (random_apply_integrable μ A hmeas M hbound y)
  map_smul' a x := by simp only [map_smul, integral_smul, RingHom.id_apply]

omit [CompleteSpace E] in
include hbound in
theorem pointwiseAverageLinearMap_bound (x : E) :
    ‖pointwiseAverageLinearMap μ A hmeas M hbound x‖ ≤ M * ‖x‖ := by
  change ‖∫ ω, A ω x ∂μ‖ ≤ M * ‖x‖
  simpa using norm_integral_le_of_norm_le_const (ae_of_all μ fun ω =>
    ((A ω).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hbound ω) (norm_nonneg x)))

/-- A genuine bounded annealed operator from pointwise measurability and
a uniform norm bound; no operator-valued Bochner integral is used. -/
def pointwiseAnnealed : E →L[ℂ] E :=
  (pointwiseAverageLinearMap μ A hmeas M hbound).mkContinuous M
    (pointwiseAverageLinearMap_bound μ A hmeas M hbound)

omit [CompleteSpace E] in
theorem pointwiseAnnealed_apply (x : E) :
    pointwiseAnnealed μ A hmeas M hbound x = ∫ ω, A ω x ∂μ := rfl

include hmeas hM hbound in
/-- The actual finite-word Fubini identity under pointwise-only Bochner
integrability, the form needed on possibly nonseparable anisotropic spaces. -/
theorem pointwiseAnnealed_pow_apply_eq_word_integral (n : ℕ) (x : E) :
    (pointwiseAnnealed μ A hmeas M hbound ^ n) x =
      ∫ w, operatorWord A n w x ∂wordMeasure μ n := by
  induction n with
  | zero =>
      change x = ∫ _w : NoiseWords Ω 0, x ∂wordMeasure μ 0
      simp
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, pointwiseAnnealed_apply, ih]
      have hint := operatorWord_apply_integrable μ A hmeas M hM hbound n x
      have hcomm (ω : Ω) : A ω (∫ w, operatorWord A n w x ∂wordMeasure μ n) =
          ∫ w, A ω (operatorWord A n w x) ∂wordMeasure μ n :=
        ((A ω).integral_comp_comm hint).symm
      simp_rw [hcomm]
      exact (integral_prod _ (operatorWord_apply_integrable μ A hmeas M hM hbound (n + 1) x)).symm

include hmeas hM hbound in
theorem pointwiseAnnealed_pow_apply_bound (n : ℕ) (x : E) (B : ℝ)
    (hword : ∀ w, ‖operatorWord A n w x‖ ≤ B) :
    ‖(pointwiseAnnealed μ A hmeas M hbound ^ n) x‖ ≤ B := by
  rw [pointwiseAnnealed_pow_apply_eq_word_integral μ A hmeas M hM hbound n x]
  simpa using norm_integral_le_of_norm_le_const (ae_of_all (wordMeasure μ n) hword)

include hmeas hM hbound in
/-- Uniform deterministic weak-word estimates give the actual averaged
power bound using only pointwise noise measurability. -/
theorem pointwiseAnnealed_geometric_power_bound (C C₀ : ℝ) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hword : ∀ n w, ‖operatorWord A n w‖ ≤ C * C₀ ^ n) :
    ∀ n, ‖pointwiseAnnealed μ A hmeas M hbound ^ n‖ ≤ C * C₀ ^ n := by
  intro n
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (pow_nonneg hC₀ n))
  intro x
  apply pointwiseAnnealed_pow_apply_bound μ A hmeas M hM hbound n x
  intro w
  exact ((operatorWord A n w).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hword n w) (norm_nonneg x))

include hmeas hM hbound in
/-- The actual two-norm Lasota--Yorke estimate, derived from cited uniform
deterministic word estimates under pointwise-only measurability. -/
theorem pointwiseAnnealed_lasota_yorke
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ι : E →L[ℂ] F) (C ρ C₀ : ℝ)
    (hword : ∀ n w x, ‖operatorWord A n w x‖ ≤
      C * ρ ^ n * ‖x‖ + C * C₀ ^ n * ‖ι x‖) :
    ∀ n x, ‖(pointwiseAnnealed μ A hmeas M hbound ^ n) x‖ ≤
      C * ρ ^ n * ‖x‖ + C * C₀ ^ n * ‖ι x‖ :=
  fun n x => pointwiseAnnealed_pow_apply_bound μ A hmeas M hM hbound n x _
    (fun w => hword n w x)

include hmeas hbound in
/-- The one-step strong-to-weak perturbation bound is also averaged
pointwise; no operator-valued Bochner measurability is needed. -/
theorem pointwiseAnnealed_weak_perturbation
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (ι : E →L[ℂ] F) (T : E →L[ℂ] E) (τ : ℝ) (hτ : 0 ≤ τ)
    (hpert : ∀ ω x, ‖ι ((A ω - T) x)‖ ≤ τ * ‖x‖) :
    ‖ι.comp (pointwiseAnnealed μ A hmeas M hbound - T)‖ ≤ τ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hτ
  intro x
  have heq : ι ((pointwiseAnnealed μ A hmeas M hbound - T) x) =
      ∫ ω, ι ((A ω - T) x) ∂μ := by
    have h := ι.integral_comp_comm
      ((random_apply_integrable μ A hmeas M hbound x).sub (integrable_const (T x)))
    simp only [Pi.sub_apply] at h
    rw [integral_sub (random_apply_integrable μ A hmeas M hbound x) (integrable_const (T x))] at h
    simpa only [sub_apply, pointwiseAnnealed_apply, integral_const, probReal_univ, one_smul]
      using h.symm
  change ‖ι ((pointwiseAnnealed μ A hmeas M hbound - T) x)‖ ≤ τ * ‖x‖
  rw [heq]
  simpa using norm_integral_le_of_norm_le_const (ae_of_all μ (fun ω => hpert ω x))

include hmeas hbound in
/-- Pointwise compatible strong and weak realizations give compatible
bounded annealed operators, without operator-valued measurability. -/
theorem pointwiseAnnealed_compatibility
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (B : Ω → F →L[ℂ] F)
    (hBmeas : ∀ y : F, AEStronglyMeasurable (fun ω => B ω y) μ)
    (Mᵥ : ℝ) (hBbound : ∀ ω, ‖B ω‖ ≤ Mᵥ) (ι : E →L[ℂ] F)
    (hcompat : ∀ ω x, ι (A ω x) = B ω (ι x)) :
    ι.comp (pointwiseAnnealed μ A hmeas M hbound) =
      (pointwiseAnnealed μ B hBmeas Mᵥ hBbound).comp ι := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, pointwiseAnnealed_apply]
  rw [← ι.integral_comp_comm (random_apply_integrable μ A hmeas M hbound x)]
  exact integral_congr_ae (ae_of_all μ fun ω => hcompat ω x)

end Pointwise

end LeanShared.AnnealedOperatorBounds
