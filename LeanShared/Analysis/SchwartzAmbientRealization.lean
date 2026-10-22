module

public import LeanShared.Analysis.AmbientLeafFamily
public import LeanShared.Analysis.SchwartzKernelBounds

/-!
# Actual Schwartz functions in the specified ambient leaf supremum

Schwartz decay above the parameter dimension gives integrability in each
ambient graph measure and a uniform bound over the supplied leaf family.
The resulting map is complex-linear on Schwartz space without assigning a
norm to that source. No compactness, distribution order bound, or comparison
with a larger family norm is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped SchwartzMap BoundedContinuousFunction

namespace LeanShared.SchwartzAmbientRealization

variable {E U A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)

/-- A fixed exponent strictly above the leaf parameter dimension. -/
def decayOrder : ℕ := Module.finrank ℝ U + 1

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
theorem decayOrder_gt : (Module.finrank ℝ U : ℝ) < (decayOrder (U := U) : ℝ) :=
  Nat.cast_lt.mpr (Nat.lt_succ_self _)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The defining Schwartz bounds supply a radial envelope. -/
theorem exists_decay (f : 𝓢(E, ℂ)) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖f x‖ ≤ D * GraphLeafNorm.radialWeight (m : ℝ) x := by
  obtain ⟨D, hD, hd⟩ := SchwartzKernelBounds.exists_uniform_translated_decay f
    (isCompact_singleton : IsCompact ({0} : Set E)) m
  refine ⟨D, hD, ?_⟩
  intro x
  simpa only [sub_zero, GraphLeafNorm.radialWeight] using hd x 0 (mem_singleton 0)

def decayConstant (f : 𝓢(E, ℂ)) : ℝ :=
  (exists_decay f (decayOrder (U := U))).choose

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace E] [BorelSpace E] in
theorem decayConstant_nonneg (f : 𝓢(E, ℂ)) : 0 ≤ decayConstant (U := U) f :=
  (exists_decay f (decayOrder (U := U))).choose_spec.1

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace E] [BorelSpace E] in
theorem decay_bound (f : 𝓢(E, ℂ)) (x : E) :
    ‖f x‖ ≤ decayConstant (U := U) f * GraphLeafNorm.radialWeight (decayOrder (U := U) : ℝ) x :=
  (exists_decay f (decayOrder (U := U))).choose_spec.2 x

/-- Every specified ambient leaf measure integrates every Schwartz test. -/
theorem integrable (f : 𝓢(E, ℂ)) (a : A) : Integrable f ((leaves a).measure μ) :=
  GraphLeafNorm.integrable_ambient μ (decayOrder_gt (U := U)) f.continuous.measurable
    (decayConstant_nonneg (U := U) f) (decay_bound (U := U) f) (leaves a)

/-- A genuine ambient L¹ supremum element for the given leaf family. -/
def realization (f : 𝓢(E, ℂ)) : GraphLeafNorm.AmbientFamilySpace μ leaves :=
  GraphLeafNorm.restrictFamily μ leaves
    (GraphLeafNorm.ambientOfDecayingFunction μ hJ (decayOrder_gt (U := U))
      f.continuous.measurable (decayConstant_nonneg (U := U) f) (decay_bound (U := U) f))

theorem realization_ae (f : 𝓢(E, ℂ)) (a : A) :
    realization μ hJ leaves f a =ᵐ[(leaves a).measure μ] f :=
  MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr (integrable μ leaves f a))

/-- The finite supremum bound is derived from decay and the common density
bound, rather than supplied as a realization hypothesis. -/
theorem realization_norm_le (f : 𝓢(E, ℂ)) :
    ‖realization μ hJ leaves f‖ ≤
      decayConstant (U := U) f * J * ∫ u, GraphLeafNorm.radialWeight (decayOrder (U := U) : ℝ) u ∂μ := by
  calc
    ‖realization μ hJ leaves f‖ ≤
        ‖GraphLeafNorm.ambientOfDecayingFunction μ hJ (decayOrder_gt (U := U))
          f.continuous.measurable (decayConstant_nonneg (U := U) f) (decay_bound (U := U) f)‖ :=
      by simpa only [realization, one_mul] using (GraphLeafNorm.restrictFamily μ leaves).le_of_opNorm_le
          (GraphLeafNorm.restrictFamily_norm_le μ leaves) _
    _ = _ := GraphLeafNorm.norm_ambientOfDecayingFunction_eq_source μ hJ (decayOrder_gt (U := U))
      f.continuous.measurable (decayConstant_nonneg (U := U) f) (decay_bound (U := U) f)
    _ ≤ _ := GraphLeafNorm.norm_ofDecayingFunction_le μ hJ (decayOrder_gt (U := U))
      f.continuous.measurable (decayConstant_nonneg (U := U) f) (decay_bound (U := U) f)

/-- Complex linearity follows from actual almost-everywhere representatives;
the chosen numerical decay bounds introduce no nonlinearity. -/
def linearMap : 𝓢(E, ℂ) →ₗ[ℂ] GraphLeafNorm.AmbientFamilySpace μ leaves where
  toFun := realization μ hJ leaves
  map_add' f g := by
    apply lp.ext
    funext a
    change realization μ hJ leaves (f + g) a =
      realization μ hJ leaves f a + realization μ hJ leaves g a
    apply Lp.ext
    filter_upwards [realization_ae μ hJ leaves (f + g) a,
      realization_ae μ hJ leaves f a, realization_ae μ hJ leaves g a,
      Lp.coeFn_add (realization μ hJ leaves f a) (realization μ hJ leaves g a)] with x hfg hf hg ha
    rw [hfg, ha]
    change f x + g x = (realization μ hJ leaves f a) x + (realization μ hJ leaves g a) x
    rw [hf, hg]
  map_smul' c f := by
    apply lp.ext
    funext a
    change realization μ hJ leaves (c • f) a = c • realization μ hJ leaves f a
    apply Lp.ext
    filter_upwards [realization_ae μ hJ leaves (c • f) a, realization_ae μ hJ leaves f a,
      Lp.coeFn_smul c (realization μ hJ leaves f a)] with x hcf hf hs
    rw [hcf, hs]
    change c * f x = c * (realization μ hJ leaves f a) x
    rw [hf]

@[simp]
theorem linearMap_ae (f : 𝓢(E, ℂ)) (a : A) :
    linearMap μ hJ leaves f a =ᵐ[(leaves a).measure μ] f := realization_ae μ hJ leaves f a

end LeanShared.SchwartzAmbientRealization
