module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexStrongFeller
public import LeanShared.Analysis.TriangularPowerBounds

/-!
# Bounded layer operators for the actual strong-Feller killed kernel

A Borel filtration split need not have continuous indicator functions.
Restriction R maps global bounded continuous functions into the product of
bounded continuous functions on the two disjoint strata. S first extends
these functions measurably by zero, then applies the actual killed kernel.
Strong-Feller regularity makes S globally continuous. Thus P = S R and
R S is genuinely triangular under the no-upward support condition. Neither
continuous gluing nor an isomorphism onto the product is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Global.LayerOperators

open ComplexStrongFeller LeanShared.TransientRestriction

variable {X 𝕜 : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [RCLike 𝕜]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (L : Set X) (hL : MeasurableSet L)

/-- Restriction itself is continuous even though measurable zero extension
usually is not. -/
def restrictOperator (U : Set X) : (X →ᵇ 𝕜) →L[𝕜] (U →ᵇ 𝕜) :=
  BoundedContinuousFunction.compContinuousCLM 𝕜 𝕜 ⟨Subtype.val, continuous_subtype_val⟩

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
@[simp] theorem restrictOperator_apply (U : Set X) (f : X →ᵇ 𝕜) (x : U) :
    restrictOperator U f x = f x.val := rfl

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
set_option maxHeartbeats 800000 in
theorem norm_restrictOperator_le_one (U : Set X) :
    ‖restrictOperator (𝕜 := 𝕜) U‖ ≤ 1 := by
  apply (restrictOperator (𝕜 := 𝕜) U).opNorm_le_bound zero_le_one
  intro f
  simpa [restrictOperator] using BoundedContinuousFunction.norm_compContinuous_le f
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))

/-- The diagonal operator on the lower stratum is actual killing on exit. -/
def lowerOperator : (L →ᵇ 𝕜) →L[𝕜] (L →ᵇ 𝕜) :=
  (restrictOperator L).comp (extensionOperator C hSF L hL)

/-- The upper diagonal kills on entrance into the lower stratum. -/
def upperOperator : ((Lᶜ : Set X) →ᵇ 𝕜) →L[𝕜] ((Lᶜ : Set X) →ᵇ 𝕜) :=
  (restrictOperator Lᶜ).comp (extensionOperator C hSF Lᶜ hL.compl)

/-- The actual transfer coupling from upper starting states into lower
endpoint observations. -/
def couplingOperator : (L →ᵇ 𝕜) →L[𝕜] ((Lᶜ : Set X) →ᵇ 𝕜) :=
  (restrictOperator Lᶜ).comp (extensionOperator C hSF L hL)

/-- Globally continuous reconstruction after one killed-kernel step. -/
def smoothAssembly : ((L →ᵇ 𝕜) × ((Lᶜ : Set X) →ᵇ 𝕜)) →L[𝕜] (X →ᵇ 𝕜) :=
  (extensionOperator C hSF L hL).comp (ContinuousLinearMap.fst 𝕜 _ _) +
    (extensionOperator C hSF Lᶜ hL.compl).comp (ContinuousLinearMap.snd 𝕜 _ _)

/-- Bounded coordinates given by restrictions to disjoint Borel strata. -/
def layerRestriction : (X →ᵇ 𝕜) →L[𝕜] ((L →ᵇ 𝕜) × ((Lᶜ : Set X) →ᵇ 𝕜)) :=
  (restrictOperator L).prod (restrictOperator Lᶜ)

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem zeroExtend_restrictions (f : X →ᵇ 𝕜) :
    zeroExtend L (restrictOperator L f) +
      zeroExtend Lᶜ (restrictOperator Lᶜ f) = (f : X → 𝕜) := by
  funext x
  by_cases hx : x ∈ L
  · change zeroExtend L (restrictOperator L f) x +
      zeroExtend Lᶜ (restrictOperator Lᶜ f) x = f x
    rw [zeroExtend_coe L _ ⟨x, hx⟩,
      zeroExtend_of_not_mem Lᶜ _ x (by simpa using hx), add_zero]
    rfl
  · change zeroExtend L (restrictOperator L f) x +
      zeroExtend Lᶜ (restrictOperator Lᶜ f) x = f x
    rw [zeroExtend_of_not_mem L _ x hx,
      zeroExtend_coe Lᶜ _ ⟨x, hx⟩, zero_add]
    rfl

/-- Exact actual transfer factorization, without discontinuous coordinates. -/
theorem transfer_eq_assembly_restriction :
    transferOperator (𝕜 := 𝕜) C hSF =
      (smoothAssembly (𝕜 := 𝕜) C hSF L hL).comp (layerRestriction (𝕜 := 𝕜) L) := by
  ext f x
  change (∫ y, f y ∂C.killedTransition x) =
    (∫ y, zeroExtend L (restrictOperator L f) y ∂C.killedTransition x) +
      ∫ y, zeroExtend Lᶜ (restrictOperator Lᶜ f) y ∂C.killedTransition x
  rw [← integral_add
    (bounded_integrable C _ (measurable_zeroExtend L hL _
      (restrictOperator L f).continuous.measurable)
      (norm_zeroExtend_le L _ (norm_nonneg _) (restrictOperator L f).norm_coe_le_norm) x)
    (bounded_integrable C _ (measurable_zeroExtend Lᶜ hL.compl _
      (restrictOperator Lᶜ f).continuous.measurable)
      (norm_zeroExtend_le Lᶜ _ (norm_nonneg _) (restrictOperator Lᶜ f).norm_coe_le_norm) x)]
  exact congrArg (fun q : X → 𝕜 => ∫ y, q y ∂C.killedTransition x)
    (zeroExtend_restrictions L f).symm

/-- Kernel support, rather than discontinuous multiplication on C⁰, gives
exactly the missing zero block. -/
theorem lower_upper_extension_eq_zero
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L) :
    (restrictOperator (𝕜 := 𝕜) L).comp
      (extensionOperator C hSF Lᶜ hL.compl) = 0 := by
  ext f x
  change (∫ y, zeroExtend Lᶜ f y ∂C.killedTransition x.val) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [hsupport x.val x.property] with y hy
  exact zeroExtend_of_not_mem Lᶜ f y (by simpa using hy)

/-- The actual bounded layer operator is triangular. -/
theorem restriction_assembly_eq_block
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L) :
    (layerRestriction (𝕜 := 𝕜) L).comp (smoothAssembly (𝕜 := 𝕜) C hSF L hL) =
      block (lowerOperator (𝕜 := 𝕜) C hSF L hL) (couplingOperator (𝕜 := 𝕜) C hSF L hL)
        (upperOperator (𝕜 := 𝕜) C hSF L hL) := by
  have hz := lower_upper_extension_eq_zero (𝕜 := 𝕜) C hSF L hL hsupport
  apply ContinuousLinearMap.ext
  intro f
  apply Prod.ext
  · change restrictOperator L (extensionOperator C hSF L hL f.1 +
      extensionOperator C hSF Lᶜ hL.compl f.2) =
      restrictOperator L (extensionOperator C hSF L hL f.1)
    rw [map_add]
    have hf := congrArg (fun T => T f.2) hz
    change restrictOperator L (extensionOperator C hSF Lᶜ hL.compl f.2) = 0 at hf
    rw [hf, add_zero]
  · exact map_add (restrictOperator Lᶜ) _ _

set_option maxHeartbeats 800000 in
/-- Every global power factors through the actual bounded triangular layers.
The extra smoothing step suffices to transfer their growth bounds. -/
theorem transfer_pow_succ
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L) (n : ℕ) :
    transferOperator (𝕜 := 𝕜) C hSF ^ (n + 1) =
      (smoothAssembly (𝕜 := 𝕜) C hSF L hL).comp
        ((block (lowerOperator (𝕜 := 𝕜) C hSF L hL) (couplingOperator (𝕜 := 𝕜) C hSF L hL)
          (upperOperator (𝕜 := 𝕜) C hSF L hL) ^ n).comp (layerRestriction (𝕜 := 𝕜) L)) := by
  induction n with
  | zero =>
      change transferOperator (𝕜 := 𝕜) C hSF = (smoothAssembly (𝕜 := 𝕜) C hSF L hL).comp
        ((ContinuousLinearMap.id 𝕜 _).comp (layerRestriction (𝕜 := 𝕜) L))
      rw [ContinuousLinearMap.id_comp]
      exact transfer_eq_assembly_restriction (𝕜 := 𝕜) C hSF L hL
  | succ n ih =>
      rw [pow_succ, ih, transfer_eq_assembly_restriction (𝕜 := 𝕜) C hSF L hL]
      apply ContinuousLinearMap.ext
      intro f
      change smoothAssembly (𝕜 := 𝕜) C hSF L hL
        ((block (lowerOperator (𝕜 := 𝕜) C hSF L hL) (couplingOperator (𝕜 := 𝕜) C hSF L hL)
          (upperOperator (𝕜 := 𝕜) C hSF L hL) ^ n)
            (layerRestriction (𝕜 := 𝕜) L (smoothAssembly (𝕜 := 𝕜) C hSF L hL (layerRestriction (𝕜 := 𝕜) L f)))) = _
      have hb := congrArg (fun T => T (layerRestriction (𝕜 := 𝕜) L f))
        (restriction_assembly_eq_block (𝕜 := 𝕜) C hSF L hL hsupport)
      change layerRestriction (𝕜 := 𝕜) L (smoothAssembly (𝕜 := 𝕜) C hSF L hL (layerRestriction (𝕜 := 𝕜) L f)) =
        block (lowerOperator (𝕜 := 𝕜) C hSF L hL) (couplingOperator (𝕜 := 𝕜) C hSF L hL)
          (upperOperator (𝕜 := 𝕜) C hSF L hL) (layerRestriction (𝕜 := 𝕜) L f) at hb
      rw [hb]
      rfl

set_option maxHeartbeats 800000 in
/-- Diagonal growth bounds for the actual killed stratum operators imply
geometric growth for the actual global transfer, at every larger rate.
No mixing hypothesis is imposed on either diagonal. -/
theorem exists_global_power_bound
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    {CA CD β γ : ℝ} (hCA : 0 ≤ CA) (hCD : 0 ≤ CD)
    (hβ : 0 < β) (hβγ : β < γ)
    (hA : ∀ n : ℕ, ‖lowerOperator (𝕜 := 𝕜) C hSF L hL ^ n‖ ≤ CA * β ^ n)
    (hD : ∀ n : ℕ, ‖upperOperator (𝕜 := 𝕜) C hSF L hL ^ n‖ ≤ CD * β ^ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ‖transferOperator (𝕜 := 𝕜) C hSF ^ n‖ ≤ K * γ ^ n := by
  obtain ⟨K, hK, hbound⟩ := LeanShared.TriangularPowerBounds.exists_geometric_block_bound
    (lowerOperator (𝕜 := 𝕜) C hSF L hL) (couplingOperator (𝕜 := 𝕜) C hSF L hL)
    (upperOperator (𝕜 := 𝕜) C hSF L hL) hCA hCD hβ hβγ hA hD
  let H := ‖smoothAssembly (𝕜 := 𝕜) C hSF L hL‖ *
    ‖layerRestriction (𝕜 := 𝕜) L‖ * K
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK
  have hγ : 0 < γ := hβ.trans hβγ
  refine ⟨‖(1 : (X →ᵇ 𝕜) →L[𝕜] (X →ᵇ 𝕜))‖ + H / γ,
    add_nonneg (norm_nonneg _) (div_nonneg hH hγ.le), ?_⟩
  intro n
  cases n with
  | zero => simp only [pow_zero, mul_one]; exact le_add_of_nonneg_right (div_nonneg hH hγ.le)
  | succ n =>
      rw [transfer_pow_succ (𝕜 := 𝕜) C hSF L hL hsupport n]
      have hb := ContinuousLinearMap.opNorm_comp_le
        (smoothAssembly (𝕜 := 𝕜) C hSF L hL)
        ((block (lowerOperator (𝕜 := 𝕜) C hSF L hL) (couplingOperator (𝕜 := 𝕜) C hSF L hL)
          (upperOperator (𝕜 := 𝕜) C hSF L hL) ^ n).comp (layerRestriction (𝕜 := 𝕜) L))
      have hi := ContinuousLinearMap.opNorm_comp_le
        (block (lowerOperator (𝕜 := 𝕜) C hSF L hL) (couplingOperator (𝕜 := 𝕜) C hSF L hL)
          (upperOperator (𝕜 := 𝕜) C hSF L hL) ^ n) (layerRestriction (𝕜 := 𝕜) L)
      calc
        _ ≤ ‖smoothAssembly (𝕜 := 𝕜) C hSF L hL‖ *
            ((K * γ ^ n) * ‖layerRestriction (𝕜 := 𝕜) L‖) :=
          hb.trans (mul_le_mul_of_nonneg_left
            (hi.trans (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))) (norm_nonneg _))
        _ = (H / γ) * γ ^ (n + 1) := by
          dsimp [H]
          rw [pow_succ]
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (norm_nonneg _)) (pow_nonneg hγ.le _)


/-- Restriction to a preserved lower level intertwines the genuine global
transfer and its killed lower diagonal. -/
theorem restriction_intertwines
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L) :
    (restrictOperator (𝕜 := 𝕜) L).comp (transferOperator (𝕜 := 𝕜) C hSF) =
      (lowerOperator C hSF L hL).comp (restrictOperator L) := by
  rw [transfer_eq_assembly_restriction (𝕜 := 𝕜) C hSF L hL]
  have hz := lower_upper_extension_eq_zero (𝕜 := 𝕜) C hSF L hL hsupport
  apply ContinuousLinearMap.ext
  intro f
  change restrictOperator L (extensionOperator C hSF L hL (restrictOperator L f) +
      extensionOperator C hSF Lᶜ hL.compl (restrictOperator Lᶜ f)) = _
  rw [map_add]
  have hzero := congrArg (fun T => T (restrictOperator (𝕜 := 𝕜) Lᶜ f)) hz
  change restrictOperator L (extensionOperator C hSF Lᶜ hL.compl
    (restrictOperator Lᶜ f)) = 0 at hzero
  rw [hzero, add_zero]
  rfl

private theorem eigenvector_eq_zero_of_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : E →L[𝕜] E) {K β : ℝ} (_hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hbound : ∀ n : ℕ, ‖A ^ n‖ ≤ K * β ^ n) (z : 𝕜) (hz : β < ‖z‖)
    (f : E) (heigen : A f = z • f) : f = 0 := by
  have hzpos : 0 < ‖z‖ := hβ.trans_lt hz
  have hpow (n : ℕ) : (A ^ n) f = z ^ n • f := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', mul_apply_eq_comp, ih, map_smul, heigen, smul_smul, pow_succ]
  have hlim : Filter.Tendsto (fun n : ℕ => K * (β / ‖z‖) ^ n * ‖f‖)
      Filter.atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hβ hzpos.le)
        ((div_lt_one hzpos).mpr hz))).mul tendsto_const_nhds
  have hf : ‖f‖ ≤ 0 := ge_of_tendsto' hlim (fun n => by
    have hnorm := (A ^ n).le_opNorm f
    rw [hpow n, norm_smul, norm_pow] at hnorm
    have hb := hnorm.trans (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg f))
    have hp : 0 < ‖z‖ ^ n := pow_pos hzpos n
    calc
      ‖f‖ ≤ (K * β ^ n * ‖f‖) / ‖z‖ ^ n := (le_div_iff₀ hp).mpr (by simpa [mul_comm] using hb)
      _ = K * (β / ‖z‖) ^ n * ‖f‖ := by rw [div_pow]; ring)
  exact norm_eq_zero.mp (le_antisymm hf (norm_nonneg f))

/-- The manuscript's dominant eigenfunction vanishes on every preserved
subordinate level whose actual transfer grows below the dominant modulus.
This conclusion uses actual layer growth rather than finite extinction. -/
theorem eigenfunction_vanishes_on_subordinate_level
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hbound : ∀ n : ℕ, ‖lowerOperator (𝕜 := 𝕜) C hSF L hL ^ n‖ ≤ K * β ^ n)
    (z : 𝕜) (hz : β < ‖z‖) (g : X →ᵇ 𝕜)
    (heigen : transferOperator (𝕜 := 𝕜) C hSF g = z • g) : ∀ x ∈ L, g x = 0 := by
  have he := congrArg (fun T => T g)
    (restriction_intertwines (𝕜 := 𝕜) C hSF L hL hsupport)
  change restrictOperator L (transferOperator (𝕜 := 𝕜) C hSF g) =
    lowerOperator C hSF L hL (restrictOperator L g) at he
  rw [heigen, map_smul] at he
  have hz := eigenvector_eq_zero_of_growth (lowerOperator (𝕜 := 𝕜) C hSF L hL)
    hK hβ hbound z hz (restrictOperator L g) he.symm
  intro x hx
  exact congrArg (fun f : L →ᵇ 𝕜 => f ⟨x, hx⟩) hz

/-- The same subordinate-level vanishing holds for every finite Jordan
order. This supplies the global spectral correspondence with no spurious
mixing assumption on the subordinate layers. -/
theorem generalized_eigenfunction_vanishes_on_subordinate_level
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hbound : ∀ n : ℕ, ‖lowerOperator (𝕜 := 𝕜) C hSF L hL ^ n‖ ≤ K * β ^ n)
    (z : 𝕜) (hz : β < ‖z‖) (k : ℕ) (g : X →ᵇ 𝕜)
    (hgen : ((transferOperator (𝕜 := 𝕜) C hSF - z • 1) ^ k) g = 0) :
    ∀ x ∈ L, g x = 0 := by
  induction k generalizing g with
  | zero =>
      have hg : g = 0 := by simpa using hgen
      intro x _hx
      rw [hg]
      rfl
  | succ k ih =>
      let Q := transferOperator (𝕜 := 𝕜) C hSF - z • 1
      have hprev : ∀ x ∈ L, (Q g) x = 0 := by
        apply ih (Q g)
        change ((transferOperator (𝕜 := 𝕜) C hSF - z • 1) ^ k)
          ((transferOperator (𝕜 := 𝕜) C hSF - z • 1) g) = 0
        rw [← mul_apply_eq_comp, ← pow_succ]
        exact hgen
      have hR : restrictOperator L (Q g) = (0 : L →ᵇ 𝕜) := by
        ext x
        exact hprev x.val x.property
      have he := congrArg (fun T => T g)
        (restriction_intertwines (𝕜 := 𝕜) C hSF L hL hsupport)
      change restrictOperator L (transferOperator (𝕜 := 𝕜) C hSF g) =
        lowerOperator C hSF L hL (restrictOperator L g) at he
      simp only [Q, sub_apply, smul_apply, one_apply_eq_self,
        map_sub, map_smul, he, sub_eq_zero] at hR
      have hzero := eigenvector_eq_zero_of_growth (lowerOperator (𝕜 := 𝕜) C hSF L hL)
        hK hβ hbound z hz (restrictOperator L g) hR
      intro x hx
      exact congrArg (fun f : L →ᵇ 𝕜 => f ⟨x, hx⟩) hzero

end ConditionedStochasticStabilityHyperbolic.Global.LayerOperators
