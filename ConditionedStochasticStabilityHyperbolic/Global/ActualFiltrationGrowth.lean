module

public import ConditionedStochasticStabilityHyperbolic.Global.FiltrationPressureConfinement
public import ConditionedStochasticStabilityHyperbolic.Global.LiveFiltrationRealization
public import ConditionedStochasticStabilityHyperbolic.Global.RelativeFiltrationGrowth

/-!
# Actual adapted-filtration strata produce live-prefix growth

The ambient finite pressure/KL output is transferred by exact nested kernel
identification to literal live-space strips. Positive-prefix support and the
proved empty live zero level supply the finite induction internally. This
removes the remaining abstract filtration-coordinate assumptions.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualFiltrationGrowth
open LeanShared ShiftedFiltrationGeometry FiltrationPressureConfinement
open LiveFiltrationRealization ComplexStrongFeller RestrictedLayerChain NestedLayerKernel RelativeFiltrationGrowth
variable {X I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ N : ℕ)
  (D : AdaptedSource T A Λ ℓ)

include hA in
/-- Beyond the finite terminal level, monotonicity forces all levels to be
whole space; measurability does not need an extra infinite-family premise. -/
theorem ambient_levels_measurable (j : ℕ) : MeasurableSet (levels T A Λ ℓ N D j) := by
  by_cases hj : j = 0
  · rw [hj, levels_zero]
    exact hA.measurableSet
  · by_cases hjℓ : j ≤ ℓ
    · exact (levels_positive_compact T A Λ ℓ N D j (Nat.pos_of_ne_zero hj) hjℓ).isClosed.measurableSet
    · have htop : D.levels j = univ := by
        apply eq_univ_of_univ_subset
        have hh := D.monotone (Nat.le_of_lt (Nat.lt_of_not_ge hjℓ))
        simpa only [D.terminal] using hh
      rw [levels, shiftedFiltration_pos T N A D.levels (Nat.pos_of_ne_zero hj), htop, preimage_univ]
      exact MeasurableSet.univ

/-- Actual ambient stratum bounds and produced adapted-prefix support give
an actual live-prefix aggregate raw-power bound, allowing all nonmixing
subordinate layers and arbitrary positive raw normalization factors. -/
theorem exists_actual_live_prefix_power_bound
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (k : ℕ) (hkℓ : k ≤ ℓ) (b : ℝ) {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ)
    (hnoUp : ∀ i, 0 < i → i ≤ k → ∀ x ∈ levels T A Λ ℓ N D i,
      C.killedTransition x (levels T A Λ ℓ N D i)ᶜ = 0)
    (hleaf : ∀ i : Fin k, ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      ‖(b • transferOperator (𝕜 := ℝ)
        (chain C (stratum T A Λ ℓ N D ⟨i.val, i.isLt.trans_le hkℓ⟩)
          (stratum_measurable T A Λ ℓ N D hA ⟨i.val, i.isLt.trans_le hkℓ⟩))
        (strongFeller C hSF (stratum T A Λ ℓ N D ⟨i.val, i.isLt.trans_le hkℓ⟩)
          (stratum_measurable T A Λ ℓ N D hA ⟨i.val, i.isLt.trans_le hkℓ⟩))) ^ n‖ ≤ B * β ^ n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      ‖(b • transferOperator (𝕜 := ℝ)
        (chain (chain C Aᶜ hA.measurableSet.compl) (liveLevels T A Λ ℓ N D k)
          ((ambient_levels_measurable T A hA Λ ℓ N D k).preimage measurable_subtype_coe))
        (strongFeller (chain C Aᶜ hA.measurableSet.compl)
          (strongFeller C hSF Aᶜ hA.measurableSet.compl) (liveLevels T A Λ ℓ N D k)
          ((ambient_levels_measurable T A hA Λ ℓ N D k).preimage measurable_subtype_coe))) ^ n‖ ≤ B * γ ^ n := by
  let CL := chain C Aᶜ hA.measurableSet.compl
  let sfL := strongFeller C hSF Aᶜ hA.measurableSet.compl
  let M := liveLevels T A Λ ℓ N D
  have hM : ∀ i, MeasurableSet (M i) := fun i =>
    (ambient_levels_measurable T A hA Λ ℓ N D i).preimage measurable_subtype_coe
  apply exists_literal_filtration_power_bound CL sfL M hM
    (liveLevels_zero T A Λ ℓ N D) (fun i => liveLevels_monotone T A Λ ℓ N D (Nat.le_succ i))
    b hβ k _ _ hβγ
  · intro i hik x hx
    by_cases hi : i = 0
    · change x ∈ liveLevels T A Λ ℓ N D i at hx
      rw [hi, liveLevels_zero] at hx
      exact hx.elim
    · have hs := live_prefix_kernel_support A C hA.measurableSet
        (levels T A Λ ℓ N D i) (ambient_levels_measurable T A hA Λ ℓ N D i)
        (hnoUp i (Nat.pos_of_ne_zero hi) hik) x hx
      apply le_antisymm _ bot_le
      exact (measure_mono (fun _ h => h.2 : M k \ M i ⊆ (M i)ᶜ)).trans_eq hs
  · intro i hik
    let j : Fin k := ⟨i, hik⟩
    let t : Fin ℓ := ⟨i, hik.trans_le hkℓ⟩
    obtain ⟨B, hB, hp⟩ := hleaf j
    refine ⟨B, hB, ?_⟩
    intro n
    have hsub : stratum T A Λ ℓ N D t ⊆ Aᶜ :=
      subset_closure.trans (closed_layer_subset_live T A Λ ℓ N D hA t)
    have he := nested_power_norm_eq (𝕜 := ℝ) (stratum T A Λ ℓ N D t) Aᶜ hsub C hSF
      (stratum_measurable T A Λ ℓ N D hA t) hA.measurableSet.compl b n
    exact he ▸ hp n

end ConditionedStochasticStabilityHyperbolic.Global.ActualFiltrationGrowth
