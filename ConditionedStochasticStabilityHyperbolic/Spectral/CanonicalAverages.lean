module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ContinuousObservables
public import LeanShared.Analysis.TransferWords
public import AbsorbingMarkovChains.FeynmanKac
import Mathlib.Tactic.Ring

/-!
# The actual canonical survival-conditioned average

The Feynman–Kac formula supplies the path/transfer-operator identity. No
irreducibility or aperiodicity hypothesis is used. The bounded continuous
transfer operator must represent the killed kernel; constructing that operator
from smooth noise and establishing its spectral gap remain explicit inputs.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset Set
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.CanonicalAverages

open AbsorbingMarkovChains AbsorbingMarkovChains.FeynmanKac
open LeanShared.TransferWords

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] (C : CanonicalChain X)

/-- The genuine time-`0,...,n-1` path average under survival through time `n`. -/
def pathAverage (h : X →ᵇ ℝ) (x : X) (n : ℕ) : ℝ :=
  ∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ range n, ext (h : X → ℝ) (ω i)
    ∂C.conditionedMeasure x n

variable (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
  (hP : ∀ (f : X →ᵇ ℝ) (x : X), (P f) x = ∫ y, f y ∂C.killedTransition x)

include hP

omit [OpensMeasurableSpace X] in
/-- The killed-kernel word is the bounded-continuous operator word. -/
theorem killedWord_eq_transferWord (φ : ℕ → (X →ᵇ ℝ)) (n : ℕ) (v : X →ᵇ ℝ) :
    killedWord C (fun i => (φ i : X → ℝ)) n (v : X → ℝ) =
      ⇑(LeanShared.TransferWords.word P φ n v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      rw [killedWord, LeanShared.TransferWords.word]
      have heq : (fun y => φ n y * ∫ z, v z ∂C.killedTransition y) =
          ((φ n * P v : X →ᵇ ℝ) : X → ℝ) := by
        funext y
        rw [← hP v y]
        rfl
      rw [heq, ih]

omit [OpensMeasurableSpace X] in
/-- The survival denominator is the `n`-step transfer of the constant one. -/
theorem survival_toReal_eq (x : X) (n : ℕ) :
    (C.pathMeasure x (CanonicalChain.survival n)).toReal = ((P ^ n) 1) x := by
  have hk := integral_prod_survival C (fun _ => fun _ => (1 : ℝ))
    (fun _ => measurable_const) zero_le_one (fun _ _ => by simp) n x
  have heq : (CanonicalChain.survival n).indicator
      (fun ω => ∏ i ∈ range n, ext (fun _ : X => (1 : ℝ)) (ω i)) =
      (CanonicalChain.survival n).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hs : ω ∈ CanonicalChain.survival n
    · rw [indicator_of_mem hs, indicator_of_mem hs]
      apply prod_eq_one
      intro i hi
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (hs i (mem_range.mp hi).le)
      simp [hy]
    · rw [indicator_of_notMem hs, indicator_of_notMem hs]
  rw [heq, integral_indicator_const _ (CanonicalChain.measurableSet_survival n)] at hk
  have hw := killedWord_eq_transferWord C P hP (fun _ => (1 : X →ᵇ ℝ)) n 1
  rw [word_eq_power P _ n (fun _ _ => rfl)] at hw
  simpa only [smul_eq_mul, mul_one, Measure.real] using hk.trans (congrFun hw x)

/-- A survival-weighted single observation has the exact two-sided operator form. -/
theorem integral_survival_observation (h : X →ᵇ ℝ) (x : X) (i n : ℕ) (hin : i < n) :
    (∫ ω, (CanonicalChain.survival n).indicator
      (fun ω => ext (h : X → ℝ) (ω i)) ω ∂C.pathMeasure x) =
      ((P ^ i) (h * ((P ^ (n - i)) 1))) x := by
  let φ : ℕ → (X →ᵇ ℝ) := singleObservation i h
  have hb (j : ℕ) (y : X) : ‖φ j y‖ ≤ max ‖h‖ 1 := by
    by_cases hj : j = i
    · simpa [φ, singleObservation, hj] using (h.norm_coe_le_norm y).trans (le_max_left _ _)
    · simp [φ, singleObservation, hj]
  have hk := integral_prod_survival C (fun j => (φ j : X → ℝ))
    (fun j => (φ j).continuous.measurable) ((norm_nonneg h).trans (le_max_left _ _))
    hb n x
  have heq : (CanonicalChain.survival n).indicator
      (fun ω => ∏ j ∈ range n, ext (φ j : X → ℝ) (ω j)) =
      (CanonicalChain.survival n).indicator (fun ω => ext (h : X → ℝ) (ω i)) := by
    funext ω
    by_cases hs : ω ∈ CanonicalChain.survival n
    · rw [indicator_of_mem hs, indicator_of_mem hs, prod_eq_single i]
      · simp [φ, singleObservation]
      · intro j hj hji
        obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (hs j (mem_range.mp hj).le)
        simp [φ, singleObservation, hji, hy]
      · exact fun hi => False.elim (hi (mem_range.mpr hin))
    · rw [indicator_of_notMem hs, indicator_of_notMem hs]
  rw [heq] at hk
  have hw := killedWord_eq_transferWord C P hP φ n 1
  rw [show φ = singleObservation i h from rfl, word_singleObservation P h i n hin 1] at hw
  exact hk.trans (congrFun hw x)

/-- The exact conditional-expectation identity, including the null-survival
totalization used by Mathlib's conditional measure. -/
theorem integral_conditioned_observation (h : X →ᵇ ℝ) (x : X) (i n : ℕ) (hin : i < n) :
    (∫ ω, ext (h : X → ℝ) (ω i) ∂C.conditionedMeasure x n) =
      ((P ^ i) (h * ((P ^ (n - i)) 1))) x / ((P ^ n) 1) x := by
  rw [CanonicalChain.conditionedMeasure, ProbabilityTheory.cond, integral_smul_measure,
    ← integral_indicator (CanonicalChain.measurableSet_survival n),
    integral_survival_observation C P hP h x i n hin, ENNReal.toReal_inv,
    survival_toReal_eq C P hP x n]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Identification of the actual path average with the ratio used in the spectral proof. -/
theorem pathAverage_eq_operatorAverage (h : X →ᵇ ℝ) (x : X) (n : ℕ) :
    pathAverage C h x n = continuousConditionedAverage P h x n := by
  let : IsFiniteMeasure (C.conditionedMeasure x n) := by
    unfold CanonicalChain.conditionedMeasure
    infer_instance
  have hi (i : ℕ) : Integrable (fun ω => ext (h : X → ℝ) (ω i))
      (C.conditionedMeasure x n) := by
    apply Integrable.of_bound
      ((measurable_ext h.continuous.measurable).comp (measurable_pi_apply i)).aestronglyMeasurable
      ‖h‖
    exact ae_of_all _ fun ω => norm_ext_le (norm_nonneg h) h.norm_coe_le_norm (ω i)
  rw [pathAverage, integral_const_mul, integral_finsetSum]
  · rw [continuousConditionedAverage_eq, mul_div_assoc]
    congr 1
    rw [sum_div]
    apply sum_congr rfl
    intro i hin
    exact integral_conditioned_observation C P hP h x i n (mem_range.mp hin)
  · intro i _
    exact hi i

omit [OpensMeasurableSpace X] in
/-- Positive limiting survival implies positive survival at every finite
horizon, using monotonicity of the genuine canonical survival events. -/
theorem survival_ne_zero (d : RankOneSpectralData P (1 : X →ᵇ ℝ))
    (x : X) (hx : 0 < d.eigenvector x) (n : ℕ) :
    C.pathMeasure x (CanonicalChain.survival n) ≠ 0 := by
  have he := d.eventually_pos_normalized_survival
    (BoundedContinuousFunction.evalCLM ℝ x) hx
  obtain ⟨m, hnm, hm⟩ := ((eventually_ge_atTop n).and he).exists
  change 0 < ((d.normalizedOperator ^ m) 1) x at hm
  simp only [RankOneSpectralData.normalizedOperator, smul_pow, smul_apply,
    BoundedContinuousFunction.smul_apply, smul_eq_mul] at hm
  have hp : 0 < ((P ^ m) 1) x :=
    (mul_pos_iff_of_pos_left (pow_pos (inv_pos.mpr d.rate_pos) m)).mp hm
  intro hn
  have hz : C.pathMeasure x (CanonicalChain.survival m) = 0 :=
    le_antisymm (hn ▸ C.survival_probability_antitone x hnm) bot_le
  rw [← survival_toReal_eq C P hP x m, hz, ENNReal.toReal_zero] at hp
  exact (lt_irrefl 0) hp

omit [OpensMeasurableSpace X] in
/-- All the conditioned path laws used in the limit are probability measures
at a starting state positive on the eigenfunction. -/
theorem conditionedMeasure_isProbability
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ))
    (x : X) (hx : 0 < d.eigenvector x) (n : ℕ) :
    IsProbabilityMeasure (C.conditionedMeasure x n) := by
  exact C.conditionedMeasure_isProbability x n (survival_ne_zero C P hP d x hx n)

/-- The genuine canonical conditional-average limit for continuous observables,
with the probability product measure from the paper's normalization. -/
theorem canonical_conditional_average_limit
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ)) (μ : Measure X) [IsFiniteMeasure μ]
    (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y) (h : X →ᵇ ℝ) (x : X)
    (hx : 0 < d.eigenvector x) :
    IsProbabilityMeasure (LeanShared.eigenvectorMeasure μ d.eigenvector) ∧
      Tendsto (pathAverage C h x) atTop
        (𝓝 (∫ y, h y ∂LeanShared.eigenvectorMeasure μ d.eigenvector)) := by
  obtain ⟨hprob, hlim⟩ := continuous_observable_probability_limit d μ hmean hg0 h x hx
  refine ⟨hprob, ?_⟩
  apply hlim.congr' (Eventually.of_forall fun n => ?_)
  exact (pathAverage_eq_operatorAverage C P hP h x n).symm

end ConditionedStochasticStabilityHyperbolic.CanonicalAverages
