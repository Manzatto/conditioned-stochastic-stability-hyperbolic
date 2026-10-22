module
public import ConditionedStochasticStabilityHyperbolic.Paper.SimpleSpectralWitness
public import ConditionedStochasticStabilityHyperbolic.Paper.NormalizedGapRenormalization
public import ConditionedStochasticStabilityHyperbolic.Spectral.RawNormalizationIndependence
public import ConditionedStochasticStabilityHyperbolic.Spectral.WeightedKernel

/-! The literal conclusions do not depend on the normalizing bound of the weighted chain. Two
bounds `R, S` of the same weight give chains whose `R`- and `S`-scaled transfer operators coincide,
whose conditioned Birkhoff averages coincide (the conditioned path law only sees ratios of the
unnormalized weight), and hence the same quasi-ergodic probabilities and simple spectral
witnesses. -/

public noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BoundedContinuousFunction Topology
namespace ConditionedStochasticStabilityHyperbolic.ChainNormalizationTransport
open AbsorbingMarkovChains AbsorbingMarkovChains.FeynmanKac LeanShared LeanShared.WeightedConditioning

variable {X : Type*} [MeasurableSpace X]

/-- The coordinate-or-one multiplier sequence. -/
def coordinate (f : X → ℝ) (k : ℕ) (i : ℕ) : X → ℝ := if i = k then f else fun _ => 1

theorem coordinate_measurable (f : X → ℝ) (hf : Measurable f) (k i : ℕ) :
    Measurable (coordinate f k i) := by
  unfold coordinate
  split_ifs
  · exact hf
  · exact measurable_const

omit [MeasurableSpace X] in
theorem coordinate_bound (f : X → ℝ) (B : ℝ) (hB : ∀ y, |f y| ≤ B) (k i : ℕ) (y : X) :
    ‖coordinate f k i y‖ ≤ max B 1 := by
  unfold coordinate
  split_ifs
  · exact (Real.norm_eq_abs (f y) ▸ hB y).trans (le_max_left _ _)
  · change ‖(1 : ℝ)‖ ≤ max B 1
    rw [norm_one]
    exact le_max_right _ _

theorem integral_coordinate (C : CanonicalChain X) (f : X → ℝ) (n k : ℕ) (hk : k < n) (x : X) :
    (∫ ω, AbsorbingMarkovChains.zeroExtension f (ω k) ∂C.conditionedMeasure x n) =
      ∫ ω, ∏ i ∈ Finset.range n, FeynmanKac.ext (coordinate f k i) (ω i) ∂C.conditionedMeasure x n := by
  apply integral_congr_ae
  filter_upwards [show ∀ᵐ ω ∂C.conditionedMeasure x n, ω ∈ CanonicalChain.survival n from
    ae_cond_mem (CanonicalChain.measurableSet_survival n)] with ω hω
  rw [Finset.prod_eq_single k]
  · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (hω k hk.le)
    simp [hy, coordinate, FeynmanKac.ext]
  · intro i hi hik
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (hω i (Finset.mem_range.mp hi).le)
    simp [hy, coordinate, FeynmanKac.ext, hik]
  · intro hk'
    exact absurd (Finset.mem_range.mpr hk) hk'

variable (K : Kernel X X) (w : X → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
  (mass : ∀ x, K x univ ≤ 1) (R S : ℝ) (hR : 0 < R) (hS : 0 < S)
  (hwR : ∀ x, w x ≤ R) (hwS : ∀ x, w x ≤ S)

/-- A conditioned Birkhoff average is the normalized sum of coordinate products. -/
theorem integral_birkhoff_eq_sum (C : CanonicalChain X) (f : X → ℝ) (hf : Measurable f) (B : ℝ)
    (hB : ∀ y, |f y| ≤ B) (n : ℕ) (x : X) :
    (∫ ω, (n : ℝ)⁻¹ * AbsorbingMarkovChains.pathBirkhoffSum f n ω ∂C.conditionedMeasure x n) =
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        ∫ ω, ∏ i ∈ Finset.range n, FeynmanKac.ext (coordinate f k i) (ω i)
          ∂C.conditionedMeasure x n := by
  have : IsFiniteMeasure (C.conditionedMeasure x n) := by
    unfold CanonicalChain.conditionedMeasure
    infer_instance
  have term : ∀ k, Integrable (fun ω : CanonicalChain.Path X =>
      AbsorbingMarkovChains.zeroExtension f (ω k)) (C.conditionedMeasure x n) := fun k =>
    Integrable.of_bound (((AbsorbingMarkovChains.measurable_zeroExtension hf).comp
      (measurable_pi_apply k)).aestronglyMeasurable) (max B 1) (Eventually.of_forall fun ω => by
        rcases h : ω k with _ | y
        · simp [zero_le_one.trans (le_max_right B 1)]
        · simpa [h, Real.norm_eq_abs] using (hB y).trans (le_max_left _ _))
  rw [integral_const_mul]
  congr 1
  have sumEq : (fun ω : CanonicalChain.Path X => AbsorbingMarkovChains.pathBirkhoffSum f n ω) =
      fun ω => ∑ k ∈ Finset.range n, AbsorbingMarkovChains.zeroExtension f (ω k) := rfl
  rw [sumEq, integral_finsetSum _ (fun k _ => term k)]
  exact Finset.sum_congr rfl fun k hk => integral_coordinate C f n k (Finset.mem_range.mp hk) x

set_option maxHeartbeats 2000000 in
include hw0 in
/-- Conditioned Birkhoff averages do not depend on the normalizer. -/
theorem conditioned_birkhoff_eq (f : X → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ y, |f y| ≤ B)
    (n : ℕ) (x : X) :
    (∫ ω, (n : ℝ)⁻¹ * AbsorbingMarkovChains.pathBirkhoffSum f n ω
        ∂(WeightedKernel.ofBoundedWeight K w R hw hR hwR mass).conditionedMeasure x n) =
      ∫ ω, (n : ℝ)⁻¹ * AbsorbingMarkovChains.pathBirkhoffSum f n ω
        ∂(WeightedKernel.ofBoundedWeight K w S hw hS hwS mass).conditionedMeasure x n := by
  have hB0 : 0 ≤ max B 1 := zero_le_one.trans (le_max_right _ _)
  have hcoord : ∀ k i, Measurable (coordinate f k i) := coordinate_measurable f hf
  have hbound : ∀ k i y, ‖coordinate f k i y‖ ≤ max B 1 := coordinate_bound f B hB
  rw [integral_birkhoff_eq_sum _ f hf B hB n x, integral_birkhoff_eq_sum _ f hf B hB n x]
  refine congrArg (fun t => (n : ℝ)⁻¹ * t) (Finset.sum_congr rfl fun k _ => ?_)
  exact (WeightedKernel.ofBoundedWeight_conditioned_product K w R hw hw0 hR hwR mass
      (coordinate f k) (hcoord k) (max B 1) hB0 (hbound k) n x).trans
    (WeightedKernel.ofBoundedWeight_conditioned_product K w S hw hw0 hS hwS mass
      (coordinate f k) (hcoord k) (max B 1) hB0 (hbound k) n x).symm

include hw0 in
/-- Quasi-ergodicity does not depend on the normalizer. -/
theorem isQuasiErgodic (ν : Measure X)
    (h : (WeightedKernel.ofBoundedWeight K w R hw hR hwR mass).IsQuasiErgodic ν) :
    (WeightedKernel.ofBoundedWeight K w S hw hS hwS mass).IsQuasiErgodic ν := by
  refine ⟨h.1, fun f hf hB => ?_⟩
  obtain ⟨B, hBf⟩ := hB
  filter_upwards [h.2 f hf ⟨B, hBf⟩] with x hx
  have same : (fun n : ℕ => ∫ ω, (n : ℝ)⁻¹ * AbsorbingMarkovChains.pathBirkhoffSum f n ω
        ∂(WeightedKernel.ofBoundedWeight K w R hw hR hwR mass).conditionedMeasure x n) =
      (fun n : ℕ => ∫ ω, (n : ℝ)⁻¹ * AbsorbingMarkovChains.pathBirkhoffSum f n ω
        ∂(WeightedKernel.ofBoundedWeight K w S hw hS hwS mass).conditionedMeasure x n) :=
    funext fun n => conditioned_birkhoff_eq K w hw hw0 mass R S hR hS hwR hwS f hf B hBf n x
  rw [← same]
  exact hx

/-- The killed kernels of two normalizations are proportional. -/
theorem ofBoundedWeight_scale (K : Kernel X X) (w : X → ℝ) (hw : Measurable w)
    (mass : ∀ x, K x univ ≤ 1) (R S : ℝ) (hR : 0 < R) (hS : 0 < S)
    (hwR : ∀ x, w x ≤ R) (hwS : ∀ x, w x ≤ S) (x : X) :
    (WeightedKernel.ofBoundedWeight K w S hw hS hwS mass).killedTransition x =
      ENNReal.ofReal (R / S) • (WeightedKernel.ofBoundedWeight K w R hw hR hwR mass).killedTransition x := by
  rw [WeightedKernel.ofBoundedWeight_killedTransition, WeightedKernel.ofBoundedWeight_killedTransition,
    normalizedKernel_apply_eq K w S hw hS, normalizedKernel_apply_eq K w R hw hR, smul_smul,
    ← ENNReal.ofReal_mul (div_nonneg hR.le hS.le)]
  congr 2
  field_simp

section Operators
variable [TopologicalSpace X] [OpensMeasurableSpace X]

/-- The scaled real transfer operator does not depend on the normalizer. -/
theorem scaled_operator_eq
    (sfR : HasStrongFellerKernel (WeightedKernel.ofBoundedWeight K w R hw hR hwR mass))
    (sfS : HasStrongFellerKernel (WeightedKernel.ofBoundedWeight K w S hw hS hwS mass)) :
    R • strongFellerTransferOperator (WeightedKernel.ofBoundedWeight K w R hw hR hwR mass) sfR =
      S • strongFellerTransferOperator (WeightedKernel.ofBoundedWeight K w S hw hS hwS mass) sfS := by
  ext f x
  change R • strongFellerTransferOperator _ sfR f x = S • strongFellerTransferOperator _ sfS f x
  rw [strongFellerTransferOperator_represents, strongFellerTransferOperator_represents,
    WeightedKernel.ofBoundedWeight_killedTransition,
    WeightedKernel.ofBoundedWeight_killedTransition,
    RawNormalizationIndependence.integral_normalized K w hw R hR,
    RawNormalizationIndependence.integral_normalized K w hw S hS,
    smul_smul, smul_smul, mul_inv_cancel₀ hR.ne', mul_inv_cancel₀ hS.ne']

end Operators

section Witness
variable [MetricSpace X] [CompactSpace X] [BorelSpace X]

/-- A simple spectral witness transports to any other normalizer. -/
def witness (ν : ProbabilityMeasure X)
    (W : Paper.LocalConclusions.SimpleSpectralWitness
      (WeightedKernel.ofBoundedWeight K w R hw hR hwR mass) R ν) :
    Paper.LocalConclusions.SimpleSpectralWitness
      (WeightedKernel.ofBoundedWeight K w S hw hS hwS mass) S ν :=
  let sfS := RawNormalizationIndependence.strongFeller K w hw mass R S hR hS hwR hwS W.strongFeller
  have e := scaled_operator_eq K w hw mass R S hR hS hwR hwS W.strongFeller sfS
  { strongFeller := sfS
    eigenfunction := W.eigenfunction
    eigenfunction_nonnegative := W.eigenfunction_nonnegative
    eigenmeasure := W.eigenmeasure
    finite_eigenmeasure := W.finite_eigenmeasure
    rate := W.rate
    rate_positive := W.rate_positive
    right := by rw [← e]; exact W.right
    left := by rw [← e]; exact W.left
    normalization := W.normalization
    product := W.product
    radius := by rw [← e]; exact W.radius
    right_unique := by rw [← e]; exact W.right_unique
    left_unique := by rw [← e]; exact W.left_unique }

end Witness

section RestrictedNoise
variable {Y Ω : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace Ω]
  (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : Y × Ω → Y) (hF : Measurable F)
  (U : Set Y) (hU : MeasurableSet U)

omit [MetricSpace Y] [BorelSpace Y] in
/-- Quasi-ergodicity of a restricted noise chain does not depend on its normalizer. -/
theorem restrictedNoise_isQuasiErgodic (w : U → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (R S : ℝ) (hR : 0 < R) (hS : 0 < S) (hwR : ∀ x, w x ≤ R) (hwS : ∀ x, w x ≤ S)
    (ν : Measure U) (h : (RestrictedNoise.chain ρ F hF U hU w hw R hR hwR).IsQuasiErgodic ν) :
    (RestrictedNoise.chain ρ F hF U hU w hw S hS hwS).IsQuasiErgodic ν :=
  isQuasiErgodic (RestrictedNoise.liveKernel ρ F hF U hU) w hw hw0
    (RestrictedNoise.liveKernel_mass_le_one ρ F hF U hU) R S hR hS hwR hwS ν h

/-- A simple spectral witness of a restricted noise chain transports to any other normalizer. -/
def restrictedNoise_witness [CompactSpace U] (w : U → ℝ) (hw : Measurable w) (R S : ℝ)
    (hR : 0 < R) (hS : 0 < S) (hwR : ∀ x, w x ≤ R) (hwS : ∀ x, w x ≤ S)
    (ν : ProbabilityMeasure U)
    (W : Paper.LocalConclusions.SimpleSpectralWitness
      (RestrictedNoise.chain ρ F hF U hU w hw R hR hwR) R ν) :
    Paper.LocalConclusions.SimpleSpectralWitness
      (RestrictedNoise.chain ρ F hF U hU w hw S hS hwS) S ν :=
  witness (RestrictedNoise.liveKernel ρ F hF U hU) w hw
    (RestrictedNoise.liveKernel_mass_le_one ρ F hF U hU) R S hR hS hwR hwS ν W

end RestrictedNoise

end ConditionedStochasticStabilityHyperbolic.ChainNormalizationTransport
