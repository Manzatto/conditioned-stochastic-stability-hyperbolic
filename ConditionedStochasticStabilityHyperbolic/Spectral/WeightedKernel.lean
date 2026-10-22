module

public import LeanShared.Probability.WeightedConditioning
public import AbsorbingMarkovChains.FeynmanKac
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Realization of bounded departure weights as absorbing chains

Every measurable kernel with mass at most one is completed by adding its
missing mass at the cemetery. Its killed kernel is exactly the original
kernel. In particular, the normalized weighted kernel gives a genuine
canonical path measure rather than a postulated process.

The measurable unweighted noise kernel remains an explicit input. This file
does not derive smoothness or the spectral gap from the perturbation family.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ConditionedStochasticStabilityHyperbolic.WeightedKernel

open AbsorbingMarkovChains LeanShared.WeightedConditioning
open AbsorbingMarkovChains.FeynmanKac

variable {X : Type*} [MeasurableSpace X]

/-- Complete a live-state transition by sending all missing mass to the cemetery. -/
def cemeteryTransition (K : Kernel X X) : Kernel (Option X) (Option X) where
  toFun
    | none => Measure.dirac none
    | some x => (K x).map Option.some + (1 - K x univ) • Measure.dirac none
  measurable' := Measure.measurable_of_measurable_coe _ fun s hs => by
    intro t ht
    change MeasurableSet (Option.some ⁻¹' ((fun z =>
      (match z with
      | none => Measure.dirac none
      | some x => (K x).map Option.some + (1 - K x univ) • Measure.dirac none) s) ⁻¹' t))
    have hm : Measurable (fun x : X =>
        ((K x).map Option.some + (1 - K x univ) • Measure.dirac none :
          Measure (Option X)) s) := by
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.map_apply measurable_some_state hs]
      exact (K.measurable_coe (hs.preimage measurable_some_state)).add
        ((measurable_const.sub (K.measurable_coe MeasurableSet.univ)).mul measurable_const)
    exact hm ht

@[simp]
theorem cemeteryTransition_none (K : Kernel X X) :
    cemeteryTransition K none = Measure.dirac none := rfl

@[simp]
theorem cemeteryTransition_some (K : Kernel X X) (x : X) :
    cemeteryTransition K (some x) =
      (K x).map Option.some + (1 - K x univ) • Measure.dirac none := rfl

/-- The missing-mass completion is a Markov kernel under the precise mass bound. -/
theorem cemeteryTransition_isMarkov (K : Kernel X X) (hK : ∀ x, K x univ ≤ 1) :
    IsMarkovKernel (cemeteryTransition K) := by
  constructor
  intro z
  cases z with
  | none => simpa only [cemeteryTransition_none] using
      (inferInstance : IsProbabilityMeasure (Measure.dirac (none : Option X)))
  | some x =>
      constructor
      have hd : (Measure.dirac (none : Option X)) univ = 1 := measure_univ
      rw [cemeteryTransition_some, Measure.add_apply, Measure.map_apply
        measurable_some_state MeasurableSet.univ, preimage_univ,
        Measure.smul_apply, hd, smul_eq_mul, mul_one]
      exact add_tsub_cancel_of_le (hK x)

/-- A canonical absorbing chain constructed from a sub-Markov transition. -/
def ofSubMarkov (K : Kernel X X) (hK : ∀ x, K x univ ≤ 1) : CanonicalChain X where
  transition := cemeteryTransition K
  markov := cemeteryTransition_isMarkov K hK
  absorbing := cemeteryTransition_none K

/-- Pulling the completed transition back to live states recovers the input exactly. -/
@[simp]
theorem ofSubMarkov_killedTransition (K : Kernel X X) (hK : ∀ x, K x univ ≤ 1) :
    (ofSubMarkov K hK).killedTransition = K := by
  ext x A hA
  rw [CanonicalChain.killedTransition_apply _ x A hA]
  change ((K x).map Option.some + (1 - K x univ) • Measure.dirac none : Measure (Option X))
    (Option.some '' A) = K x A
  have hsome := measurableEmbedding_some_state.measurableSet_image' hA
  rw [Measure.add_apply, Measure.map_apply measurable_some_state hsome,
    Measure.smul_apply, Measure.dirac_apply' _ hsome]
  simp [Set.preimage_image_eq A (fun _ _ h => Option.some.inj h)]

/-- The paper's bounded positive weights admit a canonical normalized process. -/
def ofBoundedWeight (K : Kernel X X) (w : X → ℝ) (R : ℝ)
    (hw : Measurable w) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (hK : ∀ x, K x univ ≤ 1) : CanonicalChain X :=
  ofSubMarkov (normalizedKernel K w R hw)
    (normalizedKernel_mass_le_one K w R hw hR hwR hK)

@[simp]
theorem ofBoundedWeight_killedTransition (K : Kernel X X) (w : X → ℝ) (R : ℝ)
    (hw : Measurable w) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (hK : ∀ x, K x univ ≤ 1) :
    (ofBoundedWeight K w R hw hR hwR hK).killedTransition =
      normalizedKernel K w R hw :=
  ofSubMarkov_killedTransition _ _

/-- The normalized canonical chain realizes the expected weighted one-step integral. -/
theorem ofBoundedWeight_integral (K : Kernel X X) (w : X → ℝ) (R : ℝ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hR : 0 < R)
    (hwR : ∀ x, w x ≤ R) (hK : ∀ x, K x univ ≤ 1) (f : X → ℝ) (x : X) :
    (∫ y, f y ∂(ofBoundedWeight K w R hw hR hwR hK).killedTransition x) =
      (w x / R) * ∫ y, f y ∂K x := by
  rw [ofBoundedWeight_killedTransition]
  exact integral_realWeightedKernel K (fun y => w y / R) (hw.div_const R)
    (fun y => div_nonneg (hw0 y) hR.le) f x

/-- Identification of all finite killed words for the constructed process. -/
theorem ofBoundedWeight_killedWord (K : Kernel X X) (w : X → ℝ) (R : ℝ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hR : 0 < R)
    (hwR : ∀ x, w x ≤ R) (hK : ∀ x, K x univ ≤ 1)
    (φ : ℕ → X → ℝ) (n : ℕ) (v : X → ℝ) :
    killedWord (ofBoundedWeight K w R hw hR hwR hK) φ n v =
      LeanShared.WeightedConditioning.word K (fun x => w x / R) φ n v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      rw [killedWord, LeanShared.WeightedConditioning.word]
      have he : (fun x => φ n x *
          ∫ y, v y ∂(ofBoundedWeight K w R hw hR hwR hK).killedTransition x) =
          (fun x => φ n x * (w x / R) * ∫ y, v y ∂K x) := by
        funext x
        rw [ofBoundedWeight_integral K w R hw hw0 hR hwR hK]
        ring
      rw [he, ih]

/-- The constant-one killed word is the actual finite-horizon survival mass. -/
theorem survival_toReal_eq_killedWord (C : CanonicalChain X) (n : ℕ) (x : X) :
    (C.pathMeasure x (CanonicalChain.survival n)).toReal =
      killedWord C (fun _ _ => (1 : ℝ)) n (fun _ => 1) x := by
  have hk := integral_prod_survival C (fun _ => fun _ => (1 : ℝ))
    (fun _ => measurable_const) zero_le_one (fun _ _ => by simp) n x
  have heq : (CanonicalChain.survival n).indicator
      (fun ω => ∏ i ∈ Finset.range n, ext (fun _ : X => (1 : ℝ)) (ω i)) =
      (CanonicalChain.survival n).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hs : ω ∈ CanonicalChain.survival n
    · rw [indicator_of_mem hs, indicator_of_mem hs]
      apply Finset.prod_eq_one
      intro i hi
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp
        (hs i (Finset.mem_range.mp hi).le)
      simp [hy]
    · rw [indicator_of_notMem hs, indicator_of_notMem hs]
  rw [heq, integral_indicator_const _ (CanonicalChain.measurableSet_survival n)] at hk
  simpa only [smul_eq_mul, mul_one, Measure.real] using hk

/-- Exact path/word identity for a product under the canonical conditioned law. -/
theorem integral_conditioned_product (C : CanonicalChain X) (φ : ℕ → X → ℝ)
    (hφ : ∀ i, Measurable (φ i)) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ i y, ‖φ i y‖ ≤ B) (n : ℕ) (x : X) :
    (∫ ω, ∏ i ∈ Finset.range n, ext (φ i) (ω i) ∂C.conditionedMeasure x n) =
      killedWord C φ n (fun _ => 1) x /
        killedWord C (fun _ _ => (1 : ℝ)) n (fun _ => 1) x := by
  rw [CanonicalChain.conditionedMeasure, ProbabilityTheory.cond, integral_smul_measure,
    ← integral_indicator (CanonicalChain.measurableSet_survival n),
    integral_prod_survival C φ hφ hB0 hB n x, ENNReal.toReal_inv,
    survival_toReal_eq_killedWord C n x]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The true conditioned path law realizes the unnormalized weight's ratios.
This is the cancellation needed when the potential is positive somewhere. -/
theorem ofBoundedWeight_conditioned_product (K : Kernel X X) (w : X → ℝ) (R : ℝ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hR : 0 < R)
    (hwR : ∀ x, w x ≤ R) (hK : ∀ x, K x univ ≤ 1)
    (φ : ℕ → X → ℝ) (hφ : ∀ i, Measurable (φ i)) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ i y, ‖φ i y‖ ≤ B) (n : ℕ) (x : X) :
    (∫ ω, ∏ i ∈ Finset.range n, ext (φ i) (ω i)
      ∂(ofBoundedWeight K w R hw hR hwR hK).conditionedMeasure x n) =
      conditionedWord K w φ n x := by
  rw [integral_conditioned_product _ φ hφ B hB0 hB n x,
    ofBoundedWeight_killedWord K w R hw hw0 hR hwR hK,
    ofBoundedWeight_killedWord K w R hw hw0 hR hwR hK]
  exact conditionedWord_normalized_weight K w φ n x R hR

/-- An upper-bounded real potential is shifted to a nonpositive potential.
Its exponential departure weight defines a genuine absorbing Markov chain. -/
def ofBoundedPotential (K : Kernel X X) (ψ : X → ℝ) (B : ℝ)
    (hψ : Measurable ψ) (hψB : ∀ x, ψ x ≤ B) (hK : ∀ x, K x univ ≤ 1) :
    CanonicalChain X :=
  ofBoundedWeight K (fun x => Real.exp (ψ x)) (Real.exp B) hψ.exp
    (Real.exp_pos B) (fun x => Real.exp_le_exp.mpr (hψB x)) hK

/-- The constructed chain has precisely the departure weight `exp (ψ−B)`. -/
theorem ofBoundedPotential_integral (K : Kernel X X) (ψ : X → ℝ) (B : ℝ)
    (hψ : Measurable ψ) (hψB : ∀ x, ψ x ≤ B) (hK : ∀ x, K x univ ≤ 1)
    (f : X → ℝ) (x : X) :
    (∫ y, f y ∂(ofBoundedPotential K ψ B hψ hψB hK).killedTransition x) =
      Real.exp (ψ x - B) * ∫ y, f y ∂K x := by
  unfold ofBoundedPotential
  rw [ofBoundedWeight_integral K (fun y => Real.exp (ψ y)) (Real.exp B)
    hψ.exp (fun y => (Real.exp_pos (ψ y)).le) (Real.exp_pos B)
    (fun y => Real.exp_le_exp.mpr (hψB y)) hK, Real.exp_sub]

/-- Shifting an upper-bounded potential leaves all finite conditioned products unchanged. -/
theorem ofBoundedPotential_conditioned_product (K : Kernel X X) (ψ : X → ℝ) (B : ℝ)
    (hψ : Measurable ψ) (hψB : ∀ x, ψ x ≤ B) (hK : ∀ x, K x univ ≤ 1)
    (φ : ℕ → X → ℝ) (hφ : ∀ i, Measurable (φ i)) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ i y, ‖φ i y‖ ≤ A) (n : ℕ) (x : X) :
    (∫ ω, ∏ i ∈ Finset.range n, ext (φ i) (ω i)
      ∂(ofBoundedPotential K ψ B hψ hψB hK).conditionedMeasure x n) =
      conditionedWord K (fun y => Real.exp (ψ y)) φ n x := by
  unfold ofBoundedPotential
  exact ofBoundedWeight_conditioned_product K (fun y => Real.exp (ψ y)) (Real.exp B)
    hψ.exp (fun y => (Real.exp_pos (ψ y)).le) (Real.exp_pos B)
    (fun y => Real.exp_le_exp.mpr (hψB y)) hK φ hφ A hA0 hA n x

end ConditionedStochasticStabilityHyperbolic.WeightedKernel
