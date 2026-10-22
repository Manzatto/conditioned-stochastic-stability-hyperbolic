module

public import ConditionedStochasticStabilityHyperbolic.Global.NullBoundaryLayer
public import ConditionedStochasticStabilityHyperbolic.Global.NestedLayerKernel
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedNoise

/-! # Reattaching the killed absorbing base preserves subordinate growth

A itself need not be reference-null. Its actual transition target mass is
zero by the fixed-A killed-process construction. Smoothing/restriction factors
therefore transfer actual interval growth on M minus A to the lower prefix M.
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.KilledAbsorbingBaseGrowth
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel LayerOperators NullBoundaryLayer
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Actual transition support, rather than a false volume-null assumption
on A, is the exact premise for adjoining the cemetery-only base to a prefix. -/
theorem exists_prefix_bound_of_live_interval_bound
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (A M : Set X) (hA : MeasurableSet A) (hM : MeasurableSet M)
    (hzeroA : ∀ x, C.killedTransition x A = 0)
    (b : ℝ) {B β : ℝ} (hB : 0 ≤ B) (hβ : 0 < β)
    (hpow : ∀ n : ℕ, ‖(b • transferOperator (𝕜 := ℝ)
      (chain C (M \ A) (hM.diff hA)) (strongFeller C hSF (M \ A) (hM.diff hA)))^n‖ ≤ B * β^n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ,
      ‖(b • transferOperator (𝕜 := ℝ) (chain C M hM) (strongFeller C hSF M hM))^n‖ ≤ D * β^n := by
  let CM := chain C M hM
  let sfM := strongFeller C hSF M hM
  let U := innerLevel (M \ A) M
  have hU : MeasurableSet U := (hM.diff hA).preimage measurable_subtype_coe
  have hzero : ∀ x : M, CM.killedTransition x Uᶜ = 0 := by
    intro x
    rw [RestrictedLayerChain.killedTransition,
      LeanShared.SubtypeKernel.restrict_apply_set C.killedTransition M hM x Uᶜ hU.compl]
    apply le_antisymm _ bot_le
    apply (measure_mono ?_).trans_eq (hzeroA x.val)
    rintro y ⟨z, hz, rfl⟩
    change ¬ (z.val ∈ M ∧ z.val ∉ A) at hz
    by_contra hn
    exact hz ⟨z.property, hn⟩
  let P := transferOperator (𝕜 := ℝ) CM sfM
  let Q := transferOperator (𝕜 := ℝ) (chain CM U hU) (strongFeller CM sfM U hU)
  let R := b • extensionOperator (𝕜 := ℝ) CM sfM U hU
  let S := restrictOperator (𝕜 := ℝ) U
  have hP : b • Q = S.comp R := by
    rw [show Q = lowerOperator CM sfM U hU from transferOperator_eq_lower CM sfM U hU]
    ext f y
    rfl
  have hQ : b • P = R.comp S := by
    rw [show P = (extensionOperator CM sfM U hU).comp (restrictOperator U) from
      transfer_eq_extension_restriction CM sfM U hU hzero]
    ext f y
    rfl
  have hsmall : ∀ n : ℕ, ‖(b • Q)^n‖ ≤ B * β^n := by
    intro n
    have he := nested_power_norm_eq (𝕜 := ℝ) (M \ A) M sdiff_subset C hSF (hM.diff hA) hM b n
    exact he.trans_le (hpow n)
  exact exists_power_bound_of_factor (b • Q) (b • P) R S hP hQ hB hβ hsmall

end ConditionedStochasticStabilityHyperbolic.Global.KilledAbsorbingBaseGrowth
