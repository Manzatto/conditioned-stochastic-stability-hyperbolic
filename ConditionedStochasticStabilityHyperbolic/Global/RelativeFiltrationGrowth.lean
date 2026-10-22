module

public import ConditionedStochasticStabilityHyperbolic.Global.NestedLayerKernel
public import ConditionedStochasticStabilityHyperbolic.Global.NullBoundaryLayer
import Mathlib.Tactic.Linarith

/-!
# Relative nested filtration growth

Actual successive restrictions are identified with the direct ambient
stratum kernels. Raw scaling is retained, including factors larger than one.
Leakage outside the terminal killed region is allowed.
Thus finite global growth can be obtained directly from the strips of a
literal adapted filtration rather than supplied as bounded coordinates.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Global.RelativeFiltrationGrowth

open ComplexStrongFeller LayerOperators NestedLayerKernel RestrictedLayerChain
open LeanShared.TransientRestriction

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)

set_option maxHeartbeats 800000 in
/-- Raw actual transfer growth follows from the actual two killed diagonal
bounds, through derived bounded smoothing coordinates. -/
theorem exists_raw_power_bound (L : Set X) (hL : MeasurableSet L)
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L) (b : ℝ)
    {CA CD β γ : ℝ} (hCA : 0 ≤ CA) (hCD : 0 ≤ CD) (hβ : 0 < β) (hβγ : β < γ)
    (hA : ∀ n : ℕ, ‖(b • lowerOperator (𝕜 := ℝ) C hSF L hL) ^ n‖ ≤ CA * β ^ n)
    (hD : ∀ n : ℕ, ‖(b • upperOperator (𝕜 := ℝ) C hSF L hL) ^ n‖ ≤ CD * β ^ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ‖(b • transferOperator (𝕜 := ℝ) C hSF) ^ n‖ ≤ K * γ ^ n := by
  obtain ⟨K, hK, hbound⟩ := LeanShared.TriangularPowerBounds.exists_geometric_block_bound
    (b • lowerOperator (𝕜 := ℝ) C hSF L hL) (b • couplingOperator (𝕜 := ℝ) C hSF L hL) (b • upperOperator (𝕜 := ℝ) C hSF L hL)
    hCA hCD hβ hβγ hA hD
  apply NullBoundaryLayer.exists_power_bound_of_factor
    (block (b • lowerOperator (𝕜 := ℝ) C hSF L hL) (b • couplingOperator (𝕜 := ℝ) C hSF L hL) (b • upperOperator (𝕜 := ℝ) C hSF L hL))
    (b • transferOperator (𝕜 := ℝ) C hSF) (b • smoothAssembly (𝕜 := ℝ) C hSF L hL) (layerRestriction (𝕜 := ℝ) L)
    _ _ hK (hβ.trans hβγ) hbound
  · have he := restriction_assembly_eq_block (𝕜 := ℝ) C hSF L hL hsupport
    apply ContinuousLinearMap.ext
    rintro ⟨x, y⟩
    have hh := congrArg (fun T => T (x, y)) he
    change layerRestriction (𝕜 := ℝ) L (smoothAssembly (𝕜 := ℝ) C hSF L hL (x, y)) =
      block (lowerOperator (𝕜 := ℝ) C hSF L hL) (couplingOperator (𝕜 := ℝ) C hSF L hL) (upperOperator (𝕜 := ℝ) C hSF L hL) (x, y) at hh
    change block (b • lowerOperator (𝕜 := ℝ) C hSF L hL) (b • couplingOperator (𝕜 := ℝ) C hSF L hL)
      (b • upperOperator (𝕜 := ℝ) C hSF L hL) (x, y) = layerRestriction (𝕜 := ℝ) L (b • smoothAssembly (𝕜 := ℝ) C hSF L hL (x, y))
    rw [map_smul, hh]
    change (b • (lowerOperator (𝕜 := ℝ) C hSF L hL x), b • (couplingOperator (𝕜 := ℝ) C hSF L hL x) +
      b • (upperOperator (𝕜 := ℝ) C hSF L hL y)) = b •
        (lowerOperator (𝕜 := ℝ) C hSF L hL x, couplingOperator (𝕜 := ℝ) C hSF L hL x + upperOperator (𝕜 := ℝ) C hSF L hL y)
    rw [Prod.smul_mk, smul_add]
  · rw [transfer_eq_assembly_restriction (𝕜 := ℝ) C hSF L hL]
    rfl

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- Ambient no-upward support passes to each actual restricted level. -/
theorem restricted_level_support (U V : Set X) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hsupport : ∀ x ∈ U, C.killedTransition x (V \ U) = 0) :
    ∀ x : V, x ∈ innerLevel U V → ∀ᵐ y ∂(chain C V hV).killedTransition x, y ∈ innerLevel U V := by
  intro x hx
  rw [ae_iff]
  change (chain C V hV).killedTransition x (innerLevel U V)ᶜ = 0
  rw [RestrictedLayerChain.killedTransition]
  change (LeanShared.SubtypeKernel.restrict C.killedTransition V hV x) (Subtype.val ⁻¹' U)ᶜ = 0
  rw [LeanShared.SubtypeKernel.restrict_apply_set _ V hV x _
      ((hU.preimage measurable_subtype_coe).compl)]
  apply le_antisymm _ bot_le
  calc
    _ ≤ C.killedTransition x.val (V \ U) := measure_mono (by
      rintro y ⟨v, hv, rfl⟩
      exact ⟨v.property, hv⟩)
    _ = 0 := hsupport x.val hx

private theorem chain_power_norm_congr_set (U V : Set X) (hU : MeasurableSet U)
    (hV : MeasurableSet V) (heq : U = V) (b : ℝ) (n : ℕ) :
    ‖(b • transferOperator (𝕜 := ℝ) (chain C U hU) (strongFeller C hSF U hU)) ^ n‖ =
      ‖(b • transferOperator (𝕜 := ℝ) (chain C V hV) (strongFeller C hSF V hV)) ^ n‖ := by
  subst V
  rfl

/-- The actual upper diagonal inside a level has exactly the direct
ambient strip power norms. -/
theorem relative_upper_power_norm (U V : Set X) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (b : ℝ) (n : ℕ) :
    ‖(b • upperOperator (𝕜 := ℝ) (chain C V hV) (strongFeller C hSF V hV)
      (innerLevel U V) (hU.preimage measurable_subtype_coe)) ^ n‖ =
      ‖(b • transferOperator (𝕜 := ℝ) (chain C (V \ U) (hV.diff hU))
        (strongFeller C hSF (V \ U) (hV.diff hU))) ^ n‖ := by
  have hi : innerLevel (V \ U) V = (innerLevel U V)ᶜ := by
    ext x
    simp only [innerLevel, mem_preimage, mem_sdiff, mem_compl_iff, x.property, true_and]
  have he := nested_power_norm_eq (𝕜 := ℝ) (V \ U) V sdiff_subset C hSF (hV.diff hU) hV b n
  have hr := chain_power_norm_congr_set (chain C V hV) (strongFeller C hSF V hV)
    (innerLevel (V \ U) V) (innerLevel U V)ᶜ ((hV.diff hU).preimage measurable_subtype_coe)
      (hU.preimage measurable_subtype_coe).compl hi b n
  calc
    _ = ‖(b • transferOperator (𝕜 := ℝ)
        (chain (chain C V hV) (innerLevel U V)ᶜ (hU.preimage measurable_subtype_coe).compl)
        (strongFeller (chain C V hV) (strongFeller C hSF V hV) (innerLevel U V)ᶜ
          (hU.preimage measurable_subtype_coe).compl)) ^ n‖ := by
      have hp := transferOperator_eq_lower (𝕜 := ℝ) (chain C V hV)
        (strongFeller C hSF V hV) (innerLevel U V)ᶜ
        ((hU.preimage measurable_subtype_coe).compl)
      exact (congrArg (fun P => ‖(b • P) ^ n‖) hp).symm
    _ = _ := hr.symm.trans he

/-- Literal finite filtration growth, directly from the actual disjoint
strip transfers and no-upward kernel support. All coordinate identifications
and aggregate estimates are derived, including nonmixing subordinate layers. -/
theorem exists_literal_filtration_power_bound
    (M : ℕ → Set X) (hM : ∀ i, MeasurableSet (M i)) (hzero : M 0 = ∅)
    (hnested : ∀ i, M i ⊆ M (i + 1)) (b : ℝ) {β : ℝ} (hβ : 0 < β) (k : ℕ)
    (hnoUp : ∀ i, i ≤ k → ∀ x ∈ M i, C.killedTransition x (M k \ M i) = 0)
    (hleaf : ∀ i, i < k → ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖(b • transferOperator (𝕜 := ℝ) (chain C (M (i + 1) \ M i) ((hM (i + 1)).diff (hM i)))
        (strongFeller C hSF (M (i + 1) \ M i) ((hM (i + 1)).diff (hM i)))) ^ n‖ ≤ K * β ^ n)
    {γ : ℝ} (hβγ : β < γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖(b • transferOperator (𝕜 := ℝ) (chain C (M k) (hM k))
        (strongFeller C hSF (M k) (hM k))) ^ n‖ ≤ K * γ ^ n := by
  induction k generalizing γ with
  | zero =>
      have : Subsingleton (M 0 →ᵇ ℝ) := ⟨fun f g => by
        ext x
        exact False.elim ((Set.eq_empty_iff_forall_notMem.mp hzero) x.val x.property)⟩
      refine ⟨0, le_rfl, ?_⟩
      intro n
      have hz : (b • transferOperator (𝕜 := ℝ) (chain C (M 0) (hM 0))
        (strongFeller C hSF (M 0) (hM 0))) ^ n = 0 := Subsingleton.elim _ _
      rw [hz, norm_zero, zero_mul]
  | succ k ih =>
      let η := (β + γ) / 2
      have hβη : β < η := by dsimp [η]; linarith
      have hηγ : η < γ := by dsimp [η]; linarith
      have hη : 0 < η := hβ.trans hβη
      obtain ⟨CA, hCA, hprevious⟩ := ih
        (fun i hi x hx => le_antisymm (by
          calc
            C.killedTransition x (M k \ M i) ≤ C.killedTransition x (M (k + 1) \ M i) :=
              measure_mono (sdiff_subset_sdiff_left (hnested k))
            _ = 0 := hnoUp i (Nat.le_succ_of_le hi) x hx) bot_le)
        (fun i hi => hleaf i (Nat.lt_succ_of_lt hi)) hβη
      obtain ⟨CD, hCD, hlast⟩ := hleaf k (Nat.lt_succ_self k)
      apply exists_raw_power_bound (chain C (M (k + 1)) (hM (k + 1)))
        (strongFeller C hSF (M (k + 1)) (hM (k + 1)))
        (innerLevel (M k) (M (k + 1))) ((hM k).preimage measurable_subtype_coe)
        (restricted_level_support C (M k) (M (k + 1)) (hM k) (hM (k + 1))
          (hnoUp k (Nat.le_succ k))) b hCA hCD hη hηγ
      · intro n
        rw [← transferOperator_eq_lower (chain C (M (k + 1)) (hM (k + 1)))
          (strongFeller C hSF (M (k + 1)) (hM (k + 1)))
          (innerLevel (M k) (M (k + 1))) ((hM k).preimage measurable_subtype_coe)]
        rw [nested_power_norm_eq (𝕜 := ℝ) (M k) (M (k + 1)) (hnested k) C hSF (hM k) (hM (k + 1)) b n]
        exact hprevious n
      · intro n
        rw [relative_upper_power_norm C hSF (M k) (M (k + 1)) (hM k) (hM (k + 1)) b n]
        exact (hlast n).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hβ.le hβη.le n) hCD)

end ConditionedStochasticStabilityHyperbolic.Global.RelativeFiltrationGrowth
