module

public import ConditionedStochasticStabilityHyperbolic.Global.LayerOperators
public import ConditionedStochasticStabilityHyperbolic.Global.DominantBlockGap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# From actual bounded layers to the global strong-Feller rank-one gap

The exact P = S R and B = R S relations lift the constructed layer spectral
data. The global eigenfunction and eigenfunctional are defined by S and R;
no continuous gluing or preexisting global rank-one projection is assumed.
-/

@[expose] public noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Global.LayerRankOne

section Factorization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (S : F →L[ℝ] E) (R : E →L[ℝ] F) {P : E →L[ℝ] E} {B : F →L[ℝ] F}
  (hP : P = S.comp R) (hB : B = R.comp S) {oneF : F}
  (d : RankOneSpectralData B oneF)

def liftedVector : E := d.rate⁻¹ • S d.eigenvector

def liftedMean : E →L[ℝ] ℝ := d.mean.comp R

def liftedProjection : E →L[ℝ] E := (liftedMean R d).smulRight (liftedVector S d)

include hB in
theorem lifted_mean_vector : liftedMean R d (liftedVector S d) = 1 := by
  change d.mean (R (d.rate⁻¹ • S d.eigenvector)) = 1
  rw [map_smul, map_smul]
  have he : R (S d.eigenvector) = B d.eigenvector :=
    (congrArg (fun T : F →L[ℝ] F => T d.eigenvector) hB).symm
  rw [he, d.right_eigenvector, map_smul, smul_eq_mul, smul_eq_mul, d.mean_eigenvector,
    mul_one, inv_mul_cancel₀ d.rate_pos.ne']

include hP hB in
theorem lifted_right_eigen : P (liftedVector S d) = d.rate • liftedVector S d := by
  rw [hP]
  change S (R (d.rate⁻¹ • S d.eigenvector)) = d.rate • (d.rate⁻¹ • S d.eigenvector)
  rw [map_smul, map_smul]
  have he : R (S d.eigenvector) = B d.eigenvector :=
    (congrArg (fun T : F →L[ℝ] F => T d.eigenvector) hB).symm
  rw [he, d.right_eigenvector, map_smul, smul_smul, smul_smul]
  congr 1
  exact mul_comm _ _

include hP hB in
/-- The normalized factor power formula retains one extra smoothing step. -/
theorem normalized_factor_pow (n : ℕ) :
    (d.rate⁻¹ • P) ^ (n + 1) =
      (d.rate⁻¹ • S).comp ((d.normalizedOperator ^ n).comp R) := by
  have hQ : d.rate⁻¹ • P = (d.rate⁻¹ • S).comp R := by rw [hP]; rfl
  have hD : R.comp (d.rate⁻¹ • S) = d.normalizedOperator := by
    change R.comp (d.rate⁻¹ • S) = d.rate⁻¹ • B
    calc
      _ = d.rate⁻¹ • (R.comp S) := by
        ext f
        exact R.map_smul d.rate⁻¹ (S f)
      _ = _ := congrArg (fun A : F →L[ℝ] F => d.rate⁻¹ • A) hB.symm
  induction n with
  | zero =>
      change d.rate⁻¹ • P = (d.rate⁻¹ • S).comp ((ContinuousLinearMap.id ℝ F).comp R)
      rw [ContinuousLinearMap.id_comp]
      exact hQ
  | succ n ih =>
      rw [pow_succ, ih, hQ]
      apply ContinuousLinearMap.ext
      intro f
      change (d.rate⁻¹ • S) ((d.normalizedOperator ^ n)
        (R ((d.rate⁻¹ • S) (R f)))) = _
      have he := congrArg (fun A => A (R f)) hD
      change R ((d.rate⁻¹ • S) (R f)) = d.normalizedOperator (R f) at he
      rw [he]
      rfl

theorem lifted_projection_factor :
    liftedProjection S R d = (d.rate⁻¹ • S).comp (d.projection.comp R) := by
  apply ContinuousLinearMap.ext
  intro f
  change d.mean (R f) • (d.rate⁻¹ • S d.eigenvector) =
    d.rate⁻¹ • S (d.mean (R f) • d.eigenvector)
  rw [map_smul, smul_comm]

include hP hB in
/-- A checked geometric gap of the actual bounded layers yields the global
geometric gap through the extra smoothing step. -/
theorem lifted_power_gap : ∃ (C θ : ℝ), 0 ≤ C ∧ 0 ≤ θ ∧ θ < 1 ∧
    ∀ n : ℕ, ‖(d.rate⁻¹ • P) ^ n - liftedProjection S R d‖ ≤ C * θ ^ n := by
  let θ := (d.decay + 1) / 2
  have hθ : 0 < θ := by dsimp [θ]; linarith [d.decay_nonneg]
  have hdθ : d.decay < θ := by dsimp [θ]; linarith [d.decay_lt_one]
  have hθ1 : θ < 1 := by dsimp [θ]; linarith [d.decay_lt_one]
  let H := ‖d.rate⁻¹ • S‖ * ‖R‖ * d.errorConstant
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) d.errorConstant_nonneg
  refine ⟨‖(1 : E →L[ℝ] E) - liftedProjection S R d‖ + H / θ, θ,
    add_nonneg (norm_nonneg _) (div_nonneg hH hθ.le), hθ.le, hθ1, ?_⟩
  intro n
  cases n with
  | zero =>
      simp only [pow_zero, mul_one]
      exact le_add_of_nonneg_right (div_nonneg hH hθ.le)
  | succ n =>
      have he : (d.rate⁻¹ • P) ^ (n + 1) - liftedProjection S R d =
          (d.rate⁻¹ • S).comp ((d.normalizedOperator ^ n - d.projection).comp R) := by
        rw [normalized_factor_pow S R hP hB d, lifted_projection_factor S R d]
        rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
      rw [he]
      have hb := ContinuousLinearMap.opNorm_comp_le (d.rate⁻¹ • S)
        ((d.normalizedOperator ^ n - d.projection).comp R)
      have hi := ContinuousLinearMap.opNorm_comp_le (d.normalizedOperator ^ n - d.projection) R
      calc
        _ ≤ ‖d.rate⁻¹ • S‖ * ((d.errorConstant * d.decay ^ n) * ‖R‖) :=
          hb.trans (mul_le_mul_of_nonneg_left
            (hi.trans (mul_le_mul_of_nonneg_right (d.power_gap n) (norm_nonneg _))) (norm_nonneg _))
        _ ≤ H * θ ^ n := by
          have hp := pow_le_pow_left₀ d.decay_nonneg hdθ.le n
          calc
            _ = H * d.decay ^ n := by dsimp [H]; ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hp hH
        _ = (H / θ) * θ ^ (n + 1) := by rw [pow_succ]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg _)) (pow_nonneg hθ.le _)

include hP hB in
/-- Global leading data, initially with the smoothed dominant-layer
observation. Its positive mean is derived from the local left eigenrelation. -/
def liftedData : RankOneSpectralData P (S oneF) := by
  let hg := lifted_power_gap S R hP hB d
  exact {
    rate := d.rate
    rate_pos := d.rate_pos
    mean := liftedMean R d
    eigenvector := liftedVector S d
    mean_eigenvector := lifted_mean_vector S R hB d
    mean_one_pos := by
      change 0 < d.mean (R (S oneF))
      have he : R (S oneF) = B oneF := by rw [hB]; rfl
      rw [he, d.left_eigenfunctional]
      exact mul_pos d.rate_pos d.mean_one_pos
    right_eigenvector := lifted_right_eigen S R hP hB d
    errorConstant := Classical.choose hg
    errorConstant_nonneg := (Classical.choose_spec (Classical.choose_spec hg)).1
    decay := Classical.choose (Classical.choose_spec hg)
    decay_nonneg := (Classical.choose_spec (Classical.choose_spec hg)).2.1
    decay_lt_one := (Classical.choose_spec (Classical.choose_spec hg)).2.2.1
    power_gap := (Classical.choose_spec (Classical.choose_spec hg)).2.2.2 }

end Factorization

section ConstantObservation

variable {X : Type*} [TopologicalSpace X]
  {P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)} {e : X →ᵇ ℝ}
  (d : RankOneSpectralData P e)
  (hpositive : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ P f x)

include hpositive in
private theorem normalized_powers_positive (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x)
    (n : ℕ) (x : X) : 0 ≤ ((d.normalizedOperator ^ n) f) x := by
  induction n generalizing x with
  | zero => simpa using hf x
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      change 0 ≤ d.rate⁻¹ * (P ((d.normalizedOperator ^ n) f)) x
      exact mul_nonneg (inv_nonneg.mpr d.rate_pos.le) (hpositive _ ih x)

include hpositive in
private theorem projection_positive (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : X) :
    0 ≤ d.mean f * d.eigenvector x := by
  let V : (((X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))) →L[ℝ] ℝ :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp (ContinuousLinearMap.apply ℝ (X →ᵇ ℝ) f)
  have hlim := V.continuous.continuousAt.tendsto.comp d.tendsto_powers
  have he : V d.projection = d.mean f * d.eigenvector x := rfl
  change Tendsto (fun n => ((d.normalizedOperator ^ n) f) x) atTop (𝓝 (V d.projection)) at hlim
  rw [he] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall fun n => normalized_powers_positive d hpositive f hf n x)

include hpositive in
private theorem mean_positive_on_nonneg (he : ∀ x, 0 ≤ e x)
    (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ d.mean f := by
  have hg0 (x : X) : 0 ≤ d.eigenvector x :=
    (mul_nonneg_iff_of_pos_left d.mean_one_pos).mp (projection_positive d hpositive e he x)
  have hpos : ∃ x, 0 < d.eigenvector x := by
    by_contra hn
    push Not at hn
    have hz : d.eigenvector = 0 := by
      ext x
      exact le_antisymm (hn x) (hg0 x)
    have hh := d.mean_eigenvector
    rw [hz, map_zero] at hh
    exact zero_ne_one hh
  obtain ⟨x, hx⟩ := hpos
  exact (mul_nonneg_iff_of_pos_right hx).mp (projection_positive d hpositive f hf x)

include hpositive in
/-- A nonnegative smoothed observation with positive leading mean proves
positive mean for the actual constant one. Thus the global QEM data need
no additional left-positivity assumption. -/
theorem mean_constant_one_pos (he : ∀ x, 0 ≤ e x) : 0 < d.mean (1 : X →ᵇ ℝ) := by
  have horder : ∀ x, 0 ≤ (‖e‖ • (1 : X →ᵇ ℝ) - e) x := by
    intro x
    change 0 ≤ ‖e‖ * 1 - e x
    have hb : e x ≤ ‖e‖ := (le_abs_self _).trans (e.norm_coe_le_norm x)
    linarith
  have hh := mean_positive_on_nonneg d hpositive he _ horder
  rw [map_sub, map_smul, smul_eq_mul] at hh
  by_contra hn
  have hn' : d.mean (1 : X →ᵇ ℝ) ≤ 0 := le_of_not_gt hn
  have hmul : ‖e‖ * d.mean (1 : X →ᵇ ℝ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hn'
  linarith [d.mean_one_pos]

/-- Promote the constructed smoothed observation to the literal constant
one used by conditioned averages, preserving all leading spectral data. -/
def withConstantOne (he : ∀ x, 0 ≤ e x) : RankOneSpectralData P (1 : X →ᵇ ℝ) where
  rate := d.rate
  rate_pos := d.rate_pos
  mean := d.mean
  eigenvector := d.eigenvector
  mean_eigenvector := d.mean_eigenvector
  mean_one_pos := mean_constant_one_pos d hpositive he
  right_eigenvector := d.right_eigenvector
  errorConstant := d.errorConstant
  errorConstant_nonneg := d.errorConstant_nonneg
  decay := d.decay
  decay_nonneg := d.decay_nonneg
  decay_lt_one := d.decay_lt_one
  power_gap := d.power_gap

end ConstantObservation

section ActualLayers

open ComplexStrongFeller LayerOperators LeanShared.TransientRestriction

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (L : Set X) (hL : MeasurableSet L)

theorem actual_transfer_positive (f : X →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) (x : X) :
    0 ≤ transferOperator (𝕜 := ℝ) C hSF f x := by
  rw [transferOperator_apply]
  exact integral_nonneg hf

theorem actual_assembly_nonnegative
    (obs : (L →ᵇ ℝ) × ((Lᶜ : Set X) →ᵇ ℝ))
    (hlo : ∀ x, 0 ≤ obs.1 x) (hup : ∀ x, 0 ≤ obs.2 x) :
    ∀ x, 0 ≤ smoothAssembly C hSF L hL obs x := by
  intro x
  change 0 ≤ (∫ y, zeroExtend L obs.1 y ∂C.killedTransition x) +
    ∫ y, zeroExtend Lᶜ obs.2 y ∂C.killedTransition x
  apply add_nonneg
  · apply integral_nonneg
    intro y
    by_cases hy : y ∈ L
    · rw [zeroExtend_coe L obs.1 ⟨y, hy⟩]
      exact hlo _
    · rw [zeroExtend_of_not_mem L obs.1 y hy]
      exact le_rfl
  · apply integral_nonneg
    intro y
    by_cases hy : y ∈ Lᶜ
    · rw [zeroExtend_coe Lᶜ obs.2 ⟨y, hy⟩]
      exact hup _
    · rw [zeroExtend_of_not_mem Lᶜ obs.2 y hy]
      exact le_rfl

/-- Actual strong-Feller global spectral data are constructed from the
bounded Borel-layer gap. Positivity of the killed kernel itself promotes
the smoothed local observation to the literal constant one. -/
def globalDataOfLayerData
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    (obs : (L →ᵇ ℝ) × ((Lᶜ : Set X) →ᵇ ℝ))
    (hlo : ∀ x, 0 ≤ obs.1 x) (hup : ∀ x, 0 ≤ obs.2 x)
    (d : RankOneSpectralData
      (block (lowerOperator (𝕜 := ℝ) C hSF L hL) (couplingOperator C hSF L hL)
        (upperOperator C hSF L hL)) obs) :
    RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ) :=
  withConstantOne
    (liftedData (smoothAssembly C hSF L hL) (layerRestriction L)
      (transfer_eq_assembly_restriction C hSF L hL)
      (restriction_assembly_eq_block C hSF L hL hsupport).symm d)
    (actual_transfer_positive C hSF)
    (actual_assembly_nonnegative C hSF L hL obs hlo hup)

/-- Direct local-to-global spectral producer when the dominant layer is
above the subordinate aggregate. Only the aggregate's growth is needed. -/
def globalDataWithSubordinateLower
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    (d : RankOneSpectralData (upperOperator (𝕜 := ℝ) C hSF L hL)
      (1 : (Lᶜ : Set X) →ᵇ ℝ))
    {CA β : ℝ} (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖lowerOperator (𝕜 := ℝ) C hSF L hL ^ n‖ ≤ CA * β ^ n) :
    RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ) :=
  globalDataOfLayerData C hSF L hL hsupport (0, 1) (fun _ => le_rfl) (fun _ => zero_le_one)
    (DominantBlockGap.ofSubordinateLower (lowerOperator C hSF L hL)
      (couplingOperator C hSF L hL) d hCA hβ hβr hA)

/-- Direct local-to-global spectral producer when an already constructed
lower dominant aggregate is extended by an upper subordinate aggregate. -/
def globalDataWithSubordinateUpper
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    (d : RankOneSpectralData (lowerOperator (𝕜 := ℝ) C hSF L hL) (1 : L →ᵇ ℝ))
    {CA β : ℝ} (hCA : 0 ≤ CA) (hβ : 0 ≤ β) (hβr : β < d.rate)
    (hA : ∀ n : ℕ, ‖upperOperator (𝕜 := ℝ) C hSF L hL ^ n‖ ≤ CA * β ^ n) :
    RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ) :=
  globalDataOfLayerData C hSF L hL hsupport (1, 0) (fun _ => zero_le_one) (fun _ => le_rfl)
    (DominantBlockGap.ofSubordinateUpper (upperOperator C hSF L hL)
      (couplingOperator C hSF L hL) d hCA hβ hβr hA)

end ActualLayers

end ConditionedStochasticStabilityHyperbolic.Global.LayerRankOne
