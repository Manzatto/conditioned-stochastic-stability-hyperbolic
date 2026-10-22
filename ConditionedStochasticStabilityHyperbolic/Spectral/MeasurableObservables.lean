module

public import ConditionedStochasticStabilityHyperbolic.Spectral.CanonicalAverages
import Mathlib.Tactic.FieldSimp

/-!
# Bounded measurable observations through strong-Feller smoothing

Multiplication by a measurable observation need not preserve continuous
functions. Instead the bounded operator supplied here represents one transfer
step after multiplication. Its Cesàro ratio describes observations at times
`1,...,n`, with survival through `n`. The smoothing representation and the
measurable left-eigenmeasure equation remain explicit inputs.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset Set
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smoothing observation contains one transfer step, so only `n-1`
additional powers occur in its numerator. -/
def smoothedConditionedAverage (P S : E →L[ℝ] E) (ev : E →L[ℝ] ℝ)
    (one : E) (n : ℕ) : ℝ :=
  ev (((n : ℝ)⁻¹ • ∑ i ∈ range n, P ^ i * S * P ^ (n - 1 - i)) one) /
    ev ((P ^ n) one)

/-- The observation operator contains a transfer step and must be scaled too. -/
theorem smoothedConditionedAverage_smul (c : ℝ) (hc : c ≠ 0)
    (P S : E →L[ℝ] E) (ev : E →L[ℝ] ℝ) (one : E) (n : ℕ) :
    smoothedConditionedAverage (c • P) (c • S) ev one n =
      smoothedConditionedAverage P S ev one n := by
  have hsum : (∑ i ∈ range n, (c • P) ^ i * (c • S) * (c • P) ^ (n - 1 - i)) =
      c ^ n • ∑ i ∈ range n, P ^ i * S * P ^ (n - 1 - i) := by
    rw [smul_sum]
    apply sum_congr rfl
    intro i hi
    simp only [smul_pow, smul_mul_assoc, mul_smul_comm, smul_smul]
    have hexp : i + 1 + (n - 1 - i) = n := by
      have := mem_range.mp hi
      omega
    have hcoeff : c ^ (n - 1 - i) * (c * c ^ i) = c ^ (i + 1 + (n - 1 - i)) := by
      rw [pow_add, pow_succ]
      ring
    rw [hcoeff, hexp]
  unfold smoothedConditionedAverage
  rw [hsum, smul_pow, smul_comm]
  simp only [smul_apply, map_smul, smul_eq_mul]
  exact mul_div_mul_left _ _ (pow_ne_zero n hc)

namespace RankOneSpectralData

variable {P : E →L[ℝ] E} {one : E} (d : RankOneSpectralData P one)

/-- Rank-one convergence for the exact smoothing-observation ratio. -/
theorem tendsto_smoothedConditionedAverage (S : E →L[ℝ] E)
    (ev : E →L[ℝ] ℝ) (hx : 0 < ev d.eigenvector) :
    Tendsto (smoothedConditionedAverage P S ev one) atTop
      (𝓝 (d.rate⁻¹ * d.mean (S d.eigenvector))) := by
  let Q := d.normalizedOperator
  let R := d.projection
  let A := d.rate⁻¹ • S
  let U := ‖R‖ + d.errorConstant
  have hU : 0 ≤ U := add_nonneg (norm_nonneg R) d.errorConstant_nonneg
  have hR : ‖R‖ ≤ U := le_add_of_nonneg_right d.errorConstant_nonneg
  have hQ (n : ℕ) : ‖Q ^ n‖ ≤ U := by
    calc
      ‖Q ^ n‖ ≤ ‖Q ^ n - R‖ + ‖R‖ := by
        simpa only [sub_add_cancel] using norm_add_le (Q ^ n - R) R
      _ ≤ d.errorConstant * d.decay ^ n + ‖R‖ :=
        add_le_add (d.power_gap n) le_rfl
      _ ≤ U := by
        dsimp [U]
        nlinarith [pow_le_one₀ (n := n) d.decay_nonneg d.decay_lt_one.le]
  let V := ev.comp (ContinuousLinearMap.apply ℝ E one)
  have hnum := V.continuous.continuousAt.tendsto.comp
    (AbsorbingMarkovChains.OperatorCesaro.tendsto_operator_average
      Q R A d.errorConstant_nonneg hU d.decay_nonneg d.decay_lt_one hR hQ d.power_gap)
  have hden := V.continuous.continuousAt.tendsto.comp d.tendsto_powers
  have hVP : V R = d.mean one * ev d.eigenvector := by
    simp [V, R, projection, smul_eq_mul]
  have hVpap : V (R * A * R) =
      d.mean (A d.eigenvector) * (d.mean one * ev d.eigenvector) := by
    simp [V, R, projection, mul_apply_eq_comp, smul_eq_mul]
    ring
  change Tendsto _ _ (𝓝 (V (R * A * R))) at hnum
  change Tendsto _ _ (𝓝 (V R)) at hden
  rw [hVpap] at hnum
  rw [hVP] at hden
  have hne := (mul_pos d.mean_one_pos hx).ne'
  have hlim := hnum.div hden hne
  rw [mul_div_cancel_right₀ _ hne] at hlim
  have hmean : d.mean (A d.eigenvector) = d.rate⁻¹ * d.mean (S d.eigenvector) := by
    simp [A, smul_eq_mul]
  rw [hmean] at hlim
  apply hlim.congr' (Eventually.of_forall fun n => ?_)
  exact smoothedConditionedAverage_smul d.rate⁻¹ (inv_ne_zero d.rate_pos.ne')
    P S ev one n

end RankOneSpectralData

section Kernel

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The bounded strong-Feller input needed for one bounded measurable observation. The operator
represents `P(h * f)`, not multiplication on `C_b`. -/
structure SmoothedObservable (C : AbsorbingMarkovChains.CanonicalChain X) (h : X → ℝ) where
  measurable : Measurable h
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ x, ‖h x‖ ≤ bound
  operator : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)
  represents : ∀ (f : X →ᵇ ℝ) (x : X),
    (operator f) x = ∫ y, h y * f y ∂C.killedTransition x

namespace MeasurableCanonical

open AbsorbingMarkovChains AbsorbingMarkovChains.FeynmanKac

variable (C : CanonicalChain X)
  (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
  (hP : ∀ (f : X →ᵇ ℝ) (x : X), (P f) x = ∫ y, f y ∂C.killedTransition x)

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- Read the killed transfer word from its first observation. -/
theorem killedWord_head (φ : ℕ → X → ℝ) (n : ℕ) (v : X → ℝ) :
    killedWord C φ (n + 1) v = fun x =>
      φ 0 x * ∫ y, killedWord C (fun j => φ (j + 1)) n v y ∂C.killedTransition x := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      rw [killedWord, ih]
      rfl

include hP

omit [OpensMeasurableSpace X] in
theorem killedWord_one (n : ℕ) (v : X →ᵇ ℝ) :
    killedWord C (fun _ _ => (1 : ℝ)) n (v : X → ℝ) = ⇑((P ^ n) v) := by
  have hw := CanonicalAverages.killedWord_eq_transferWord C P hP
    (fun _ => (1 : X →ᵇ ℝ)) n v
  rw [LeanShared.TransferWords.word_eq_power P _ n (fun _ _ => rfl)] at hw
  exact hw

variable {h : X → ℝ} (s : SmoothedObservable C h)

omit [OpensMeasurableSpace X] in
theorem killedWord_one_measurable_terminal (n : ℕ) (v : X →ᵇ ℝ) :
    killedWord C (fun _ _ => (1 : ℝ)) (n + 1) (fun y => h y * v y) =
      ⇑((P ^ n) (s.operator v)) := by
  induction n with
  | zero =>
      funext x
      simpa only [killedWord, one_mul, pow_zero, one_apply_eq_self] using
        (s.represents v x).symm
  | succ n ih =>
      rw [killedWord_head, ih]
      funext x
      simp only [one_mul]
      rw [← hP, pow_succ', mul_apply_eq_comp]

omit [OpensMeasurableSpace X] in
/-- The single measurable observation at time zero is allowed to remain
measurable; a subsequent backward transfer smooths it. -/
theorem killedWord_single_zero (n : ℕ) (v : X →ᵇ ℝ) :
    killedWord C (fun j y => if j = 0 then h y else 1) (n + 1) (v : X → ℝ) =
      fun y => h y * ((P ^ (n + 1)) v) y := by
  rw [killedWord_head]
  have hshift : (fun j y => if j + 1 = 0 then h y else (1 : ℝ)) =
      (fun _ _ => (1 : ℝ)) := by
    funext j y
    simp
  rw [hshift, killedWord_one C P hP]
  funext x
  simp only [ite_true]
  rw [← hP, pow_succ', mul_apply_eq_comp]

omit [OpensMeasurableSpace X] in
/-- After at least one transition the single measurable factor is smoothed. -/
theorem killedWord_single_positive (i n : ℕ) (hin : i + 1 < n) (v : X →ᵇ ℝ) :
    killedWord C (fun j y => if j = i + 1 then h y else 1) n (v : X → ℝ) =
      ⇑((P ^ i) (s.operator ((P ^ (n - (i + 1))) v))) := by
  induction i generalizing n with
  | zero =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [killedWord_head]
      have hshift : (fun j y => if j + 1 = 0 + 1 then h y else (1 : ℝ)) =
          (fun j y => if j = 0 then h y else 1) := by
        funext j y
        simp
      rw [hshift, killedWord_single_zero C P hP]
      funext x
      have hexp : k.succ.succ - (0 + 1) = k + 1 := by omega
      rw [hexp]
      simpa only [show (0 : ℕ) ≠ 0 + 1 by omega, ite_false, one_mul,
        pow_zero, one_apply_eq_self, Nat.add_sub_cancel] using
        (s.represents ((P ^ (k + 1)) v) x).symm
  | succ i ih =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [killedWord_head]
      have hshift : (fun j y => if j + 1 = i + 1 + 1 then h y else (1 : ℝ)) =
          (fun j y => if j = i + 1 then h y else 1) := by
        funext j y
        simp
      rw [hshift, ih m (by omega)]
      funext x
      simp only [show (0 : ℕ) ≠ (i + 1) + 1 by omega, ite_false, one_mul]
      have hexp : m.succ - (i.succ + 1) = m - (i + 1) := by omega
      rw [hexp]
      rw [← hP, pow_succ', mul_apply_eq_comp]

omit [OpensMeasurableSpace X] in
/-- Exact survival-weighted observation after the first transition and
strictly before the last. -/
theorem integral_survival_observation_positive (x : X) (i n : ℕ) (hin : i + 1 < n) :
    (∫ ω, (CanonicalChain.survival n).indicator
      (fun ω => ext h (ω (i + 1))) ω ∂C.pathMeasure x) =
      ((P ^ i) (s.operator ((P ^ (n - (i + 1))) 1))) x := by
  let φ : ℕ → X → ℝ := fun j y => if j = i + 1 then h y else 1
  have hm (j : ℕ) : Measurable (φ j) := by
    dsimp [φ]
    split_ifs
    · exact s.measurable
    · exact measurable_const
  have hb (j : ℕ) (y : X) : ‖φ j y‖ ≤ max s.bound 1 := by
    dsimp [φ]
    split_ifs
    · exact (s.norm_le y).trans (le_max_left _ _)
    · simp [le_max_right s.bound 1]
  have hk := integral_prod_survival C φ hm (s.bound_nonneg.trans (le_max_left _ _))
    hb n x
  have heq : (CanonicalChain.survival n).indicator
      (fun ω => ∏ j ∈ range n, ext (φ j) (ω j)) =
      (CanonicalChain.survival n).indicator (fun ω => ext h (ω (i + 1))) := by
    funext ω
    by_cases hs : ω ∈ CanonicalChain.survival n
    · rw [indicator_of_mem hs, indicator_of_mem hs, prod_eq_single (i + 1)]
      · simp [φ]
      · intro j hj hji
        obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (hs j (mem_range.mp hj).le)
        simp [φ, hji, hy]
      · exact fun hi => False.elim (hi (mem_range.mpr hin))
    · rw [indicator_of_notMem hs, indicator_of_notMem hs]
  rw [heq] at hk
  have hw := killedWord_single_positive C P hP s i n hin 1
  exact hk.trans (congrFun hw x)

omit [OpensMeasurableSpace X] in
/-- The last observation is represented by the terminal factor in the
Feynman–Kac formula, including paths killed before the horizon. -/
theorem integral_survival_observation_terminal (x : X) (n : ℕ) :
    (∫ ω, (CanonicalChain.survival (n + 1)).indicator
      (fun ω => ext h (ω (n + 1))) ω ∂C.pathMeasure x) =
      ((P ^ n) (s.operator 1)) x := by
  have hk := integral_prod_eq_killedWord C (fun _ _ => (1 : ℝ))
    (fun _ => measurable_const) zero_le_one (fun _ _ => by simp) (n + 1)
    s.measurable s.bound_nonneg s.norm_le x
  have heq : (fun ω => (∏ j ∈ range (n + 1), ext (fun _ : X => (1 : ℝ)) (ω j)) *
      ext h (ω (n + 1))) =ᵐ[C.pathMeasure x]
      (CanonicalChain.survival (n + 1)).indicator (fun ω => ext h (ω (n + 1))) := by
    filter_upwards [C.ae_mem_survival_iff x (n + 1)] with ω hω
    by_cases hs : ω ∈ CanonicalChain.survival (n + 1)
    · rw [indicator_of_mem hs]
      have hp : (∏ j ∈ range (n + 1), ext (fun _ : X => (1 : ℝ)) (ω j)) = 1 := by
        apply prod_eq_one
        intro j hj
        obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (hs j (mem_range.mp hj).le)
        simp [hy]
      rw [hp, one_mul]
    · have hn : ω (n + 1) = none := by
        by_contra hn
        exact hs (hω.2 hn)
      simp [indicator_of_notMem hs, hn]
  rw [integral_congr_ae heq] at hk
  have hw := killedWord_one_measurable_terminal C P hP s n 1
  have hw' : killedWord C (fun _ _ => (1 : ℝ)) (n + 1) h =
      ⇑((P ^ n) (s.operator 1)) := by simpa using hw
  exact hk.trans (congrFun hw' x)

omit [OpensMeasurableSpace X] in
/-- The exact conditioned transfer formula for observations at times `1,...,n`. -/
theorem integral_conditioned_observation_shifted (x : X) (i n : ℕ) (hin : i < n) :
    (∫ ω, ext h (ω (i + 1)) ∂C.conditionedMeasure x n) =
      ((P ^ i) (s.operator ((P ^ (n - 1 - i)) 1))) x / ((P ^ n) 1) x := by
  rw [CanonicalChain.conditionedMeasure, ProbabilityTheory.cond, integral_smul_measure,
    ← integral_indicator (CanonicalChain.measurableSet_survival n), ENNReal.toReal_inv,
    CanonicalAverages.survival_toReal_eq C P hP x n]
  have hi : (∫ ω, (CanonicalChain.survival n).indicator
      (fun ω => ext h (ω (i + 1))) ω ∂C.pathMeasure x) =
      ((P ^ i) (s.operator ((P ^ (n - 1 - i)) 1))) x := by
    by_cases hlast : i + 1 = n
    · subst n
      simpa using integral_survival_observation_terminal C P hP s x i
    · have hexp : n - (i + 1) = n - 1 - i := by omega
      simpa only [hexp] using
        integral_survival_observation_positive C P hP s x i n (by omega)
  rw [hi]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Genuine bounded measurable path average, with the shifted time window. -/
def shiftedPathAverage (h : X → ℝ) (x : X) (n : ℕ) : ℝ :=
  ∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ range n, ext h (ω (i + 1)) ∂C.conditionedMeasure x n

omit [OpensMeasurableSpace X] in
/-- Smoothing identifies the operator ratio with its actual conditioned path law. -/
theorem shiftedPathAverage_eq (x : X) (n : ℕ) :
    shiftedPathAverage C h x n = smoothedConditionedAverage P s.operator
      (BoundedContinuousFunction.evalCLM ℝ x) 1 n := by
  let : IsFiniteMeasure (C.conditionedMeasure x n) := by
    unfold CanonicalChain.conditionedMeasure
    infer_instance
  have hi (i : ℕ) : Integrable (fun ω => ext h (ω (i + 1)))
      (C.conditionedMeasure x n) := by
    apply Integrable.of_bound
      ((measurable_ext s.measurable).comp (measurable_pi_apply (i + 1))).aestronglyMeasurable
      s.bound
    exact ae_of_all _ fun ω => norm_ext_le s.bound_nonneg s.norm_le (ω (i + 1))
  rw [shiftedPathAverage, integral_const_mul, integral_finsetSum]
  · simp only [smoothedConditionedAverage, smul_apply, map_smul,
      smul_eq_mul, BoundedContinuousFunction.evalCLM_apply,
      _root_.sum_apply, BoundedContinuousFunction.sum_apply,
      mul_apply_eq_comp]
    rw [mul_div_assoc, sum_div]
    congr 1
    apply sum_congr rfl
    intro i hin
    exact integral_conditioned_observation_shifted C P hP s x i n (mem_range.mp hin)
  · intro i _
    exact hi i

/-- The paper's unshifted measurable path average. -/
def pathAverage (h : X → ℝ) (x : X) (n : ℕ) : ℝ :=
  ∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ range n, ext h (ω i) ∂C.conditionedMeasure x n

omit [OpensMeasurableSpace X] in
/-- The two time windows differ by just two bounded endpoint observations. -/
theorem pathAverage_sub_shifted_bound
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ)) (x : X)
    (hx : 0 < d.eigenvector x) (n : ℕ) :
    ‖pathAverage C h x n - shiftedPathAverage C h x n‖ ≤
      (n : ℝ)⁻¹ * (2 * s.bound) := by
  let : IsProbabilityMeasure (C.conditionedMeasure x n) :=
    CanonicalAverages.conditionedMeasure_isProbability C P hP d x hx n
  have hi (i : ℕ) : Integrable (fun ω => ext h (ω i)) (C.conditionedMeasure x n) := by
    apply Integrable.of_bound
      ((measurable_ext s.measurable).comp (measurable_pi_apply i)).aestronglyMeasurable s.bound
    exact ae_of_all _ fun ω => norm_ext_le s.bound_nonneg s.norm_le (ω i)
  have havg : Integrable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ range n, ext h (ω i))
      (C.conditionedMeasure x n) :=
    (integrable_finsetSum _ (fun i _ => hi i)).const_mul _
  have hshift : Integrable (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ range n, ext h (ω (i + 1)))
      (C.conditionedMeasure x n) :=
    (integrable_finsetSum _ (fun i _ => hi (i + 1))).const_mul _
  rw [pathAverage, shiftedPathAverage, ← integral_sub havg hshift]
  have hb : ∀ᵐ ω ∂C.conditionedMeasure x n,
      ‖(n : ℝ)⁻¹ * ∑ i ∈ range n, ext h (ω i) -
        (n : ℝ)⁻¹ * ∑ i ∈ range n, ext h (ω (i + 1))‖ ≤
          (n : ℝ)⁻¹ * (2 * s.bound) := by
    apply ae_of_all
    intro ω
    have htel : (∑ i ∈ range n, ext h (ω (i + 1))) -
        (∑ i ∈ range n, ext h (ω i)) = ext h (ω n) - ext h (ω 0) := by
      rw [← sum_sub_distrib]
      exact sum_range_sub (fun i => ext h (ω i)) n
    have heq : (n : ℝ)⁻¹ * ∑ i ∈ range n, ext h (ω i) -
        (n : ℝ)⁻¹ * ∑ i ∈ range n, ext h (ω (i + 1)) =
        (n : ℝ)⁻¹ * (ext h (ω 0) - ext h (ω n)) := by
      rw [← mul_sub]
      congr 1
      linarith [htel]
    rw [heq, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
    exact (norm_sub_le _ _).trans (by
      have hzero := norm_ext_le s.bound_nonneg s.norm_le (ω 0)
      have hn := norm_ext_le s.bound_nonneg s.norm_le (ω n)
      linarith)
  simpa using norm_integral_le_of_norm_le_const hb

end MeasurableCanonical

/-- A genuinely bounded measurable observable has the smoothed transfer-ratio
limit, provided the eigenmeasure equation holds for that measurable product. -/
theorem measurable_observable_operator_limit
    (C : AbsorbingMarkovChains.CanonicalChain X)
    {P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)}
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ))
    (μ : Measure X) [IsFiniteMeasure μ]
    (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y)
    {h : X → ℝ} (s : SmoothedObservable C h)
    (hleft : (∫ x, ∫ y, h y * d.eigenvector y ∂C.killedTransition x ∂μ) =
      d.rate * ∫ y, h y * d.eigenvector y ∂μ)
    (x : X) (hx : 0 < d.eigenvector x) :
    IsProbabilityMeasure (LeanShared.eigenvectorMeasure μ d.eigenvector) ∧
      Tendsto (smoothedConditionedAverage P s.operator
        (BoundedContinuousFunction.evalCLM ℝ x) 1) atTop
        (𝓝 (∫ y, h y ∂LeanShared.eigenvectorMeasure μ d.eigenvector)) := by
  refine ⟨eigenvector_product_isProbability d μ hmean hg0, ?_⟩
  have hlim := d.tendsto_smoothedConditionedAverage s.operator
    (BoundedContinuousFunction.evalCLM ℝ x) hx
  have heq : d.rate⁻¹ * d.mean (s.operator d.eigenvector) =
      ∫ y, h y ∂LeanShared.eigenvectorMeasure μ d.eigenvector := by
    rw [hmean]
    simp_rw [s.represents]
    rw [hleft, ← mul_assoc, inv_mul_cancel₀ d.rate_pos.ne', one_mul,
      LeanShared.integral_eigenvectorMeasure μ d.eigenvector
        d.eigenvector.continuous.measurable hg0]
  rw [heq] at hlim
  exact hlim

end Kernel

section CanonicalLimit

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The actual survival-conditioned average for every bounded measurable
observable supplied with a bounded strong-Feller smoothing operator. Its
time window is exactly `0,...,n-1`, as in the manuscript. -/
theorem canonical_measurable_average_limit
    (C : AbsorbingMarkovChains.CanonicalChain X)
    {P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)}
    (hP : ∀ (f : X →ᵇ ℝ) (x : X), (P f) x = ∫ y, f y ∂C.killedTransition x)
    (d : RankOneSpectralData P (1 : X →ᵇ ℝ))
    (μ : Measure X) [IsFiniteMeasure μ]
    (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y)
    {h : X → ℝ} (s : SmoothedObservable C h)
    (hleft : (∫ x, ∫ y, h y * d.eigenvector y ∂C.killedTransition x ∂μ) =
      d.rate * ∫ y, h y * d.eigenvector y ∂μ)
    (x : X) (hx : 0 < d.eigenvector x) :
    IsProbabilityMeasure (LeanShared.eigenvectorMeasure μ d.eigenvector) ∧
      Tendsto (MeasurableCanonical.pathAverage C h x) atTop
        (𝓝 (∫ y, h y ∂LeanShared.eigenvectorMeasure μ d.eigenvector)) := by
  obtain ⟨hprob, hlim⟩ := measurable_observable_operator_limit C d μ hmean hg0 s hleft x hx
  have hshift : Tendsto (MeasurableCanonical.shiftedPathAverage C h x) atTop
      (𝓝 (∫ y, h y ∂LeanShared.eigenvectorMeasure μ d.eigenvector)) := by
    apply hlim.congr' (Eventually.of_forall fun n => ?_)
    exact (MeasurableCanonical.shiftedPathAverage_eq C P hP s x n).symm
  have hzero : Tendsto (fun n : ℕ => MeasurableCanonical.pathAverage C h x n -
      MeasurableCanonical.shiftedPathAverage C h x n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (MeasurableCanonical.pathAverage_sub_shifted_bound C P hP s d x hx)
    simpa using tendsto_inv_atTop_nhds_zero_nat.mul_const (2 * s.bound)
  refine ⟨hprob, ?_⟩
  have hs := hzero.add hshift
  simpa only [sub_add_cancel, zero_add] using hs

end CanonicalLimit

end ConditionedStochasticStabilityHyperbolic
