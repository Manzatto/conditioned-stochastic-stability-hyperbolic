module

public import ConditionedStochasticStabilityHyperbolic.Global.RestrictedLayerChain
public import ConditionedStochasticStabilityHyperbolic.Global.LayerQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedNoise

/-!
# Conditioned full-process correspondence on an invariant prefix

The original cemetery remains fixed. Actual live kernel support inside a
measurable prefix makes added killing upon exit ineffective at every finite
horizon. No assumption is made about transitions starting outside the prefix.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.PrefixCorrespondence
open AbsorbingMarkovChains RestrictedLayerChain RestrictedNoise
variable {X : Type*} [MeasurableSpace X]
  (C : CanonicalChain X) (U : Set X) (hU : MeasurableSet U)
  (hsupport : ∀ x ∈ U, C.killedTransition x Uᶜ = 0)

include hsupport in
/-- Every actual prefix transition agrees under state-space inclusion. -/
theorem integral_compatible (f : X → ℝ) (x : U) :
    (∫ y, f y.val ∂(chain C U hU).killedTransition x) =
      ∫ y, f y ∂C.killedTransition x.val := by
  rw [RestrictedLayerChain.killedTransition]
  rw [← (MeasurableEmbedding.subtype_coe hU).integral_map f,
    LeanShared.SubtypeKernel.map_restrict_apply]
  have hs : ∀ᵐ y ∂C.killedTransition x.val, y ∈ U := by
    simpa only [mem_compl_iff, not_not] using
      (measure_eq_zero_iff_ae_notMem.mp (hsupport x.val x.property))
  rw [Measure.restrict_eq_self_of_ae_mem hs]

include hsupport in
/-- Every finite killed observation word agrees without extra exit killing. -/
theorem killedWord_compatible (φ : ℕ → X → ℝ) (n : ℕ) (v : X → ℝ) :
    FeynmanKac.killedWord (chain C U hU) (fun i y => φ i y.val) n (fun y => v y.val) =
      fun y => FeynmanKac.killedWord C φ n v y.val := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      rw [FeynmanKac.killedWord, FeynmanKac.killedWord]
      have he : (fun y : U => φ n y.val * ∫ z, v z.val ∂(chain C U hU).killedTransition y) =
          (fun y : U => φ n y.val * ∫ z, v z ∂C.killedTransition y.val) := by
        funext y
        rw [integral_compatible C U hU hsupport v y]
      rw [he]
      exact ih (fun y => φ n y * ∫ z, v z ∂C.killedTransition y)

include hsupport in
/-- All bounded measurable finite conditioned products agree, including
zero-survival totalization. -/
theorem conditioned_product_eq (φ : ℕ → X → ℝ) (hφ : ∀ i, Measurable (φ i))
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ i y, ‖φ i y‖ ≤ B) (n : ℕ) (x : U) :
    (∫ ω, ∏ i ∈ Finset.range n, FeynmanKac.ext (fun y : U => φ i y.val) (ω i)
      ∂(chain C U hU).conditionedMeasure x n) =
      ∫ ω, ∏ i ∈ Finset.range n, FeynmanKac.ext (φ i) (ω i) ∂C.conditionedMeasure x.val n := by
  rw [WeightedKernel.integral_conditioned_product (chain C U hU)
      (fun i y => φ i y.val) (fun i => (hφ i).comp measurable_subtype_coe) B hB0
      (fun i y => hB i y.val) n x,
    WeightedKernel.integral_conditioned_product C φ hφ B hB0 hB n x.val]
  rw [killedWord_compatible C U hU hsupport φ n (fun _ => 1),
    killedWord_compatible C U hU hsupport (fun _ _ => 1) n (fun _ => 1)]

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

include hsupport in
/-- Every observation strictly before the conditioning horizon agrees. -/
theorem conditioned_observation_eq (h : X → ℝ) (hh : Measurable h)
    (B : ℝ) (hB : ∀ y, ‖h y‖ ≤ B) (n i : ℕ) (hi : i < n) (x : U) :
    (∫ ω, FeynmanKac.ext (fun y : U => h y.val) (ω i)
      ∂(chain C U hU).conditionedMeasure x n) =
      ∫ ω, FeynmanKac.ext h (ω i)
        ∂(C).conditionedMeasure x.val n := by
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
  have he := conditioned_product_eq C U hU hsupport
    φ hφ (max B 1) (zero_le_one.trans (le_max_right _ _)) hb n x
  change (∫ ω, ∏ j ∈ Finset.range n,
      FeynmanKac.ext (fun y : U => if j = i then h y.val else 1) (ω j)
      ∂(chain C U hU).conditionedMeasure x n) =
      ∫ ω, ∏ j ∈ Finset.range n,
        FeynmanKac.ext (fun y => if j = i then h y else 1) (ω j)
        ∂(C).conditionedMeasure x.val n at he
  rw [integral_conditioned_single_product _ _ n i hi x,
    integral_conditioned_single_product _ _ n i hi x.val] at he
  exact he

include hsupport in
/-- Exact agreement of the manuscript's time-`0,...,n-1` conditioned averages. -/
theorem conditioned_average_eq (h : X → ℝ) (hh : Measurable h)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ y, ‖h y‖ ≤ B) (n : ℕ) (x : U) :
    (∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      FeynmanKac.ext (fun y : U => h y.val) (ω i)
      ∂(chain C U hU).conditionedMeasure x n) =
      ∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, FeynmanKac.ext h (ω i)
        ∂(C).conditionedMeasure x.val n := by
  have hs (i : ℕ) := integrable_conditioned_observation
    (chain C U hU) (fun y : U => h y.val)
    (hh.comp measurable_subtype_coe) B hB0 (fun y => hB y.val) n i x
  have ha (i : ℕ) := integrable_conditioned_observation
    (C) h hh B hB0 hB n i x.val
  rw [integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ => hs i), integral_finsetSum _ (fun i _ => ha i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact conditioned_observation_eq C U hU hsupport
    h hh B hB n i (Finset.mem_range.mp hi) x

include hsupport in
/-- Exact horizon survival masses agree before and after prefix restriction. -/
theorem survival_probability_eq (n : ℕ) (x : U) :
    (chain C U hU).pathMeasure x (CanonicalChain.survival n) =
      C.pathMeasure x.val (CanonicalChain.survival n) := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [WeightedKernel.survival_toReal_eq_killedWord,
    WeightedKernel.survival_toReal_eq_killedWord,
    killedWord_compatible C U hU hsupport (fun _ _ => 1) n (fun _ => 1)]

section Limit
variable [MetricSpace X] [BorelSpace X] [CompactSpace U]
  (hSF : HasStrongFellerKernel (chain C U hU))

include hsupport in
/-- The checked prefix spectral/QEM theorem gives the full-process limit
from every positive-basin starting state inside the prefix. The absorbing
region and actual exponential weight remain those of the original process. -/
theorem full_process_limit_from_prefix
    (d : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ)
      (chain C U hU) hSF) (1 : U →ᵇ ℝ))
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ B : ℝ, ∀ y, ‖f y‖ ≤ B)
    (x : U) (hx : 0 < d.eigenvector x) :
    Tendsto (MeasurableCanonical.pathAverage C f x.val) atTop
      (𝓝 (∫ y, f y ∂(LayerQuasiErgodic.productMeasure (chain C U hU) hSF d).map Subtype.val)) := by
  have hlim := LayerQuasiErgodic.conditioned_average_limit (chain C U hU) hSF d
    (fun y => f y.val) (hf.comp measurable_subtype_coe)
    (by obtain ⟨B, hB⟩ := hb; exact ⟨B, fun y => hB y.val⟩) x hx
  rw [(MeasurableEmbedding.subtype_coe hU).integral_map f]
  convert hlim using 1
  funext n
  obtain ⟨B, hB⟩ := hb
  exact (conditioned_average_eq C U hU hsupport f hf (max B 0)
    (le_max_right _ _) (fun y => (hB y).trans (le_max_left _ _)) n x).symm

end Limit

end ConditionedStochasticStabilityHyperbolic.Global.PrefixCorrespondence
