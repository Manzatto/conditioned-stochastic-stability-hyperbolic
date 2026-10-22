module

public import LeanShared.Probability.SubtypeKernel
public import ConditionedStochasticStabilityHyperbolic.Spectral.NoiseKernel

/-!
# The literal live state space of a killed noisy process

The live type is the measurable subtype `U`, and the canonical state type is
`Option U`. Both weights and observables may be defined only on `U`. For an
ambient compatible weight, the killed-kernel powers, survival probabilities,
and conditioned finite products agree with the ambient chain.

These results do not assume the random maps preserve `U`: exits are sent to
the canonical cemetery. Compatibility of ambient weights is required only
at live starting states.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ConditionedStochasticStabilityHyperbolic.RestrictedNoise

open AbsorbingMarkovChains LeanShared.RandomMapKernel LeanShared.WeightedConditioning

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X) (hF : Measurable F)
  (U : Set X) (hU : MeasurableSet U)

/-- The unweighted one-step law pulled back to the actual live-state type. -/
def liveKernel : Kernel U U := LeanShared.SubtypeKernel.restrict (transition ρ F hF) U hU

theorem liveKernel_mass_le_one (x : U) : liveKernel ρ F hF U hU x univ ≤ 1 :=
  LeanShared.SubtypeKernel.restrict_mass_le_one _ U hU (fun _ => by simp) x

/-- The cemetery is adjoined to `U`, with the departure weight defined only there. -/
def chain (w : U → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R)
    (hwR : ∀ x, w x ≤ R) : CanonicalChain U :=
  WeightedKernel.ofBoundedWeight (liveKernel ρ F hF U hU) w R hw hR hwR
    (liveKernel_mass_le_one ρ F hF U hU)

/-- An explicit compatible ambient realization, using zero extension of the live weight. -/
def ambientChain (w : U → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R)
    (hwR : ∀ x, w x ≤ R) : CanonicalChain X :=
  NoiseKernel.chain ρ F hF U hU (LeanShared.SubtypeKernel.zeroExtend U w)
    (LeanShared.SubtypeKernel.measurable_zeroExtend U hU w hw) R hR
    (LeanShared.SubtypeKernel.zeroExtend_le U w R hR.le hwR)

@[simp]
theorem killedTransition (w : U → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R)
    (hwR : ∀ x, w x ≤ R) :
    (chain ρ F hF U hU w hw R hR hwR).killedTransition =
      normalizedKernel (liveKernel ρ F hF U hU) w R hw :=
  WeightedKernel.ofBoundedWeight_killedTransition _ _ _ _ _ _ _

/-- The exact noise integral, including the exit indicator and subtype-only observable. -/
theorem integral_chain (w : U → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (f : U → ℝ) (hf : Measurable f) (x : U) :
    (∫ y, f y ∂(chain ρ F hF U hU w hw R hR hwR).killedTransition x) =
      (w x / R) * ∫ ω, U.indicator (LeanShared.SubtypeKernel.zeroExtend U f)
        (F (x.val, ω)) ∂ρ := by
  rw [chain, WeightedKernel.ofBoundedWeight_integral _ w R hw hw0 hR hwR]
  rw [liveKernel, LeanShared.SubtypeKernel.integral_restrict, ← integral_indicator hU]
  rw [integral_transition ρ F hF _
    ((LeanShared.SubtypeKernel.measurable_zeroExtend U hU f hf).indicator hU)]

/-- A single finite product factor is exactly the indicated observation under survival. -/
theorem integral_conditioned_single_product (C : CanonicalChain X) (h : X → ℝ)
    (n i : ℕ) (hi : i < n) (x : X) :
    (∫ ω, ∏ j ∈ Finset.range n,
      FeynmanKac.ext (fun y => if j = i then h y else 1) (ω j)
      ∂C.conditionedMeasure x n) =
      ∫ ω, FeynmanKac.ext h (ω i) ∂C.conditionedMeasure x n := by
  apply integral_congr_ae
  filter_upwards [C.ae_survival_conditionedMeasure x n] with ω hω
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (hω j (Finset.mem_range.mp hj).le)
    simp [hji, hy]
  · intro hin
    exact False.elim (hin (Finset.mem_range.mpr hi))

/-- The conditioned word identity also includes an observable at the final
time `n`, so it covers all coordinates of the finite surviving history. -/
theorem integral_conditioned_terminal_product (C : CanonicalChain X)
    (φ : ℕ → X → ℝ) (hφ : ∀ i, Measurable (φ i)) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ i y, ‖φ i y‖ ≤ A) (v : X → ℝ) (hv : Measurable v)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ y, ‖v y‖ ≤ B) (n : ℕ) (x : X) :
    (∫ ω, (∏ i ∈ Finset.range n, FeynmanKac.ext (φ i) (ω i)) *
      FeynmanKac.ext v (ω n) ∂C.conditionedMeasure x n) =
      FeynmanKac.killedWord C φ n v x /
        FeynmanKac.killedWord C (fun _ _ => (1 : ℝ)) n (fun _ => 1) x := by
  have hind : (CanonicalChain.survival n).indicator
      (fun ω => (∏ i ∈ Finset.range n, FeynmanKac.ext (φ i) (ω i)) *
        FeynmanKac.ext v (ω n)) =ᵐ[C.pathMeasure x]
      (fun ω => (∏ i ∈ Finset.range n, FeynmanKac.ext (φ i) (ω i)) *
        FeynmanKac.ext v (ω n)) := by
    filter_upwards [C.ae_mem_survival_iff x n] with ω hω
    by_cases hs : ω ∈ CanonicalChain.survival n
    · rw [indicator_of_mem hs]
    · have hn : ω n = none := by
        by_contra h
        exact hs (hω.mpr h)
      rw [indicator_of_notMem hs, hn, FeynmanKac.ext_none, mul_zero]
  rw [CanonicalChain.conditionedMeasure, ProbabilityTheory.cond, integral_smul_measure,
    ← integral_indicator (CanonicalChain.measurableSet_survival n), integral_congr_ae hind,
    FeynmanKac.integral_prod_eq_killedWord C φ hφ hA0 hA n hv hB0 hB x,
    ENNReal.toReal_inv, WeightedKernel.survival_toReal_eq_killedWord C n x]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem integrable_conditioned_observation {Y : Type*} [MeasurableSpace Y]
    (C : CanonicalChain Y) (h : Y → ℝ) (hh : Measurable h) (B : ℝ)
    (hB0 : 0 ≤ B) (hB : ∀ y, ‖h y‖ ≤ B) (n i : ℕ) (x : Y) :
    Integrable (fun ω => FeynmanKac.ext h (ω i)) (C.conditionedMeasure x n) := by
  let : IsFiniteMeasure (C.conditionedMeasure x n) := by
    unfold CanonicalChain.conditionedMeasure
    infer_instance
  apply Integrable.of_bound
    ((FeynmanKac.measurable_ext hh).comp (measurable_pi_apply i)).aestronglyMeasurable B
  exact ae_of_all _ fun ω => FeynmanKac.norm_ext_le hB0 hB (ω i)

section Correspondence

variable (w : U → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R)
  (hwR : ∀ x, w x ≤ R)
  (wa : X → ℝ) (hwa : Measurable wa) (hwaR : ∀ x, wa x ≤ R)
  (hcompat : ∀ x : U, wa x.val = w x)

include hcompat in
/-- The literal live kernel is the pullback of the compatible ambient weighted kernel. -/
theorem killedTransition_eq_restrict :
    (chain ρ F hF U hU w hw R hR hwR).killedTransition =
      LeanShared.SubtypeKernel.restrict
        (NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR).killedTransition U hU := by
  ext x A hA
  rw [killedTransition, LeanShared.SubtypeKernel.restrict_apply_set _ U hU x A hA,
    NoiseKernel.chain, WeightedKernel.ofBoundedWeight_killedTransition]
  simp only [normalizedKernel, realWeightedKernel_apply, Measure.smul_apply, smul_eq_mul,
    hcompat]
  rw [liveKernel, LeanShared.SubtypeKernel.restrict_apply_set _ U hU x A hA]
  have hi : Subtype.val '' A ⊆ U := by
    rintro y ⟨z, _, rfl⟩
    exact z.property
  change _ = _ * ((transition ρ F hF x.val).restrict U) (Subtype.val '' A)
  rw [Measure.restrict_eq_self _ hi]

/-- The ambient killed transition has no mass outside the survival region. -/
theorem ambient_killedTransition_supported (x : X) :
    ((NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR).killedTransition x).restrict U =
      (NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR).killedTransition x := by
  rw [NoiseKernel.chain, WeightedKernel.ofBoundedWeight_killedTransition]
  simp only [normalizedKernel, realWeightedKernel_apply, Measure.restrict_smul]
  change _ • (((transition ρ F hF x).restrict U).restrict U) =
    _ • (transition ρ F hF x).restrict U
  rw [Measure.restrict_restrict hU, inter_self]

include hcompat in
/-- Every finite killed endpoint law is preserved by the state-space inclusion. -/
theorem map_killedTransition_pow (n : ℕ) (x : U) :
    (((chain ρ F hF U hU w hw R hR hwR).killedTransition ^ n) x).map Subtype.val =
      ((NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR).killedTransition ^ n) x.val := by
  rw [killedTransition_eq_restrict ρ F hF U hU w hw R hR hwR wa hwa hwaR hcompat]
  exact LeanShared.SubtypeKernel.map_restrict_pow_apply _ U hU
    (ambient_killedTransition_supported ρ F hF U hU R hR wa hwa hwaR) n x

include hcompat in
/-- Actual survival probabilities agree at every horizon, including time zero. -/
theorem survival_probability_eq (n : ℕ) (x : U) :
    (chain ρ F hF U hU w hw R hR hwR).pathMeasure x (CanonicalChain.survival n) =
      (NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR).pathMeasure x.val
        (CanonicalChain.survival n) := by
  rw [CanonicalChain.pathMeasure_survival, CanonicalChain.pathMeasure_survival]
  have he := congrArg (fun μ : Measure X => μ univ)
    (map_killedTransition_pow ρ F hF U hU w hw R hR hwR wa hwa hwaR hcompat n x)
  simpa only [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    preimage_univ] using he

include hcompat in
/-- Integration of a compatible ambient observable agrees at one killed step. -/
theorem integral_killedTransition_compatible (f : X → ℝ) (x : U) :
    (∫ y, f y.val ∂(chain ρ F hF U hU w hw R hR hwR).killedTransition x) =
      ∫ y, f y ∂(NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR).killedTransition x.val := by
  rw [killedTransition_eq_restrict ρ F hF U hU w hw R hR hwR wa hwa hwaR hcompat]
  exact LeanShared.SubtypeKernel.integral_restrict_supported _ U hU
    (ambient_killedTransition_supported ρ F hF U hU R hR wa hwa hwaR) f x

include hcompat in
/-- All finite observation words agree under live-state inclusion. -/
theorem killedWord_compatible (φ : ℕ → X → ℝ) (n : ℕ) (v : X → ℝ) :
    FeynmanKac.killedWord (chain ρ F hF U hU w hw R hR hwR)
      (fun i y => φ i y.val) n (fun y => v y.val) =
      fun y => FeynmanKac.killedWord
        (NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR) φ n v y.val := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      rw [FeynmanKac.killedWord, FeynmanKac.killedWord]
      have he : (fun y : U => φ n y.val *
          ∫ z, v z.val ∂(chain ρ F hF U hU w hw R hR hwR).killedTransition y) =
          (fun y : U => φ n y.val * ∫ z, v z
            ∂(NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR).killedTransition y.val) := by
        funext y
        rw [integral_killedTransition_compatible ρ F hF U hU w hw R hR hwR
          wa hwa hwaR hcompat v y]
      rw [he]
      exact ih (fun y => φ n y * ∫ z, v z
        ∂(NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR).killedTransition y)

include hcompat in
/-- The actual survival-conditioned endpoint events agree for every measurable set. -/
theorem conditioned_endpoint_eq (n : ℕ) (x : U) (A : Set X) (hA : MeasurableSet A) :
    (chain ρ F hF U hU w hw R hR hwR).conditionedMeasure x n
      {ω | ω n ∈ Option.some '' (Subtype.val ⁻¹' A)} =
      (NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR).conditionedMeasure x.val n
        {ω | ω n ∈ Option.some '' A} := by
  rw [CanonicalChain.conditionedMeasure_endpoint _ x n _ (hA.preimage measurable_subtype_coe),
    CanonicalChain.conditionedMeasure_endpoint _ x.val n A hA]
  have hm := map_killedTransition_pow ρ F hF U hU w hw R hR hwR
    wa hwa hwaR hcompat n x
  have hnum := congrArg (fun μ : Measure X => μ A) hm
  rw [Measure.map_apply measurable_subtype_coe hA] at hnum
  have hden := congrArg (fun μ : Measure X => μ univ) hm
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ] at hden
  rw [hnum, hden]

include hcompat in
/-- The genuine conditioned finite products agree, including null-survival totalization. -/
theorem conditioned_product_eq (φ : ℕ → X → ℝ) (hφ : ∀ i, Measurable (φ i))
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ i y, ‖φ i y‖ ≤ B) (n : ℕ) (x : U) :
    (∫ ω, ∏ i ∈ Finset.range n, FeynmanKac.ext (fun y : U => φ i y.val) (ω i)
      ∂(chain ρ F hF U hU w hw R hR hwR).conditionedMeasure x n) =
      ∫ ω, ∏ i ∈ Finset.range n, FeynmanKac.ext (φ i) (ω i)
        ∂(NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR).conditionedMeasure x.val n := by
  have hφU (i : ℕ) : Measurable (fun y : U => φ i y.val) :=
    (hφ i).comp measurable_subtype_coe
  rw [WeightedKernel.integral_conditioned_product (chain ρ F hF U hU w hw R hR hwR)
      (fun (i : ℕ) (y : U) => φ i y.val) hφU B hB0 (fun i y => hB i y.val) n x,
    WeightedKernel.integral_conditioned_product
      (NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR) φ hφ B hB0 hB n x.val]
  rw [killedWord_compatible ρ F hF U hU w hw R hR hwR wa hwa hwaR hcompat φ n
      (fun _ => 1),
    killedWord_compatible ρ F hF U hU w hw R hR hwR wa hwa hwaR hcompat
      (fun _ _ => 1) n (fun _ => 1)]

include hcompat in
/-- Conditioned products over every coordinate `0,...,n`, including the
terminal observation, agree between the two canonical state spaces. -/
theorem conditioned_terminal_product_eq (φ : ℕ → X → ℝ)
    (hφ : ∀ i, Measurable (φ i)) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ i y, ‖φ i y‖ ≤ A) (v : X → ℝ) (hv : Measurable v)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ y, ‖v y‖ ≤ B) (n : ℕ) (x : U) :
    (∫ ω, (∏ i ∈ Finset.range n,
      FeynmanKac.ext (fun y : U => φ i y.val) (ω i)) *
      FeynmanKac.ext (fun y : U => v y.val) (ω n)
      ∂(chain ρ F hF U hU w hw R hR hwR).conditionedMeasure x n) =
      ∫ ω, (∏ i ∈ Finset.range n, FeynmanKac.ext (φ i) (ω i)) *
        FeynmanKac.ext v (ω n)
        ∂(NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR).conditionedMeasure x.val n := by
  have hφU (i : ℕ) : Measurable (fun y : U => φ i y.val) :=
    (hφ i).comp measurable_subtype_coe
  rw [integral_conditioned_terminal_product (chain ρ F hF U hU w hw R hR hwR)
      (fun (i : ℕ) (y : U) => φ i y.val) hφU A hA0 (fun i y => hA i y.val)
      (fun y : U => v y.val) (hv.comp measurable_subtype_coe) B hB0
      (fun y => hB y.val) n x,
    integral_conditioned_terminal_product
      (NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR)
      φ hφ A hA0 hA v hv B hB0 hB n x.val]
  rw [killedWord_compatible ρ F hF U hU w hw R hR hwR wa hwa hwaR hcompat φ n v,
    killedWord_compatible ρ F hF U hU w hw R hR hwR wa hwa hwaR hcompat
      (fun _ _ => 1) n (fun _ => 1)]

include hcompat in
/-- Every observation strictly before the conditioning horizon agrees. -/
theorem conditioned_observation_eq (h : X → ℝ) (hh : Measurable h)
    (B : ℝ) (hB : ∀ y, ‖h y‖ ≤ B) (n i : ℕ) (hi : i < n) (x : U) :
    (∫ ω, FeynmanKac.ext (fun y : U => h y.val) (ω i)
      ∂(chain ρ F hF U hU w hw R hR hwR).conditionedMeasure x n) =
      ∫ ω, FeynmanKac.ext h (ω i)
        ∂(NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR).conditionedMeasure x.val n := by
  let φ : ℕ → X → ℝ := fun j y => if j = i then h y else 1
  have hφ (j : ℕ) : Measurable (φ j) := by
    dsimp [φ]
    split_ifs
    · exact hh
    · exact measurable_const
  have hb (j : ℕ) (y : X) : ‖φ j y‖ ≤ max B 1 := by
    dsimp [φ]
    split_ifs
    · exact (hB y).trans (le_max_left _ _)
    · simpa only [abs_one] using le_max_right B (1 : ℝ)
  have he := conditioned_product_eq ρ F hF U hU w hw R hR hwR wa hwa hwaR hcompat
    φ hφ (max B 1) (zero_le_one.trans (le_max_right _ _)) hb n x
  change (∫ ω, ∏ j ∈ Finset.range n,
      FeynmanKac.ext (fun y : U => if j = i then h y.val else 1) (ω j)
      ∂(chain ρ F hF U hU w hw R hR hwR).conditionedMeasure x n) =
      ∫ ω, ∏ j ∈ Finset.range n,
        FeynmanKac.ext (fun y => if j = i then h y else 1) (ω j)
        ∂(NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR).conditionedMeasure x.val n at he
  rw [integral_conditioned_single_product _ _ n i hi x,
    integral_conditioned_single_product _ _ n i hi x.val] at he
  exact he

include hcompat in
/-- Exact agreement of the manuscript's time-`0,...,n-1` conditioned averages. -/
theorem conditioned_average_eq (h : X → ℝ) (hh : Measurable h)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ y, ‖h y‖ ≤ B) (n : ℕ) (x : U) :
    (∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      FeynmanKac.ext (fun y : U => h y.val) (ω i)
      ∂(chain ρ F hF U hU w hw R hR hwR).conditionedMeasure x n) =
      ∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, FeynmanKac.ext h (ω i)
        ∂(NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR).conditionedMeasure x.val n := by
  have hs (i : ℕ) := integrable_conditioned_observation
    (chain ρ F hF U hU w hw R hR hwR) (fun y : U => h y.val)
    (hh.comp measurable_subtype_coe) B hB0 (fun y => hB y.val) n i x
  have ha (i : ℕ) := integrable_conditioned_observation
    (NoiseKernel.chain ρ F hF U hU wa hwa R hR hwaR) h hh B hB0 hB n i x.val
  rw [integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ => hs i), integral_finsetSum _ (fun i _ => ha i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact conditioned_observation_eq ρ F hF U hU w hw R hR hwR wa hwa hwaR hcompat
    h hh B hB n i (Finset.mem_range.mp hi) x

end Correspondence

/-- No ambient weight is required to obtain the finite-horizon survival correspondence. -/
theorem survival_probability_eq_ambientChain (w : U → ℝ) (hw : Measurable w)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) (n : ℕ) (x : U) :
    (chain ρ F hF U hU w hw R hR hwR).pathMeasure x (CanonicalChain.survival n) =
      (ambientChain ρ F hF U hU w hw R hR hwR).pathMeasure x.val
        (CanonicalChain.survival n) :=
  survival_probability_eq ρ F hF U hU w hw R hR hwR
    (LeanShared.SubtypeKernel.zeroExtend U w)
    (LeanShared.SubtypeKernel.measurable_zeroExtend U hU w hw)
    (LeanShared.SubtypeKernel.zeroExtend_le U w R hR.le hwR)
    (LeanShared.SubtypeKernel.zeroExtend_coe U w) n x

/-- A bounded measurable observable defined only on the live region has the
same actual conditioned average as its explicit ambient zero extension. -/
theorem conditioned_average_eq_ambientChain (w : U → ℝ) (hw : Measurable w)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (f : U → ℝ) (hf : Measurable f) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ y, ‖f y‖ ≤ B) (n : ℕ) (x : U) :
    (∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, FeynmanKac.ext f (ω i)
      ∂(chain ρ F hF U hU w hw R hR hwR).conditionedMeasure x n) =
      ∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        FeynmanKac.ext (LeanShared.SubtypeKernel.zeroExtend U f) (ω i)
        ∂(ambientChain ρ F hF U hU w hw R hR hwR).conditionedMeasure x.val n := by
  have he := conditioned_average_eq ρ F hF U hU w hw R hR hwR
    (LeanShared.SubtypeKernel.zeroExtend U w)
    (LeanShared.SubtypeKernel.measurable_zeroExtend U hU w hw)
    (LeanShared.SubtypeKernel.zeroExtend_le U w R hR.le hwR)
    (LeanShared.SubtypeKernel.zeroExtend_coe U w)
    (LeanShared.SubtypeKernel.zeroExtend U f)
    (LeanShared.SubtypeKernel.measurable_zeroExtend U hU f hf)
    B hB0 (LeanShared.SubtypeKernel.norm_zeroExtend_le U f B hB0 hB) n x
  have hfext : (fun y : U => LeanShared.SubtypeKernel.zeroExtend U f y.val) = f := by
    funext y
    exact LeanShared.SubtypeKernel.zeroExtend_coe U f y
  rw [hfext] at he
  exact he

end ConditionedStochasticStabilityHyperbolic.RestrictedNoise
