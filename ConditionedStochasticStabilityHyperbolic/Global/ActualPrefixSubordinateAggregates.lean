module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualFiltrationIntervalGrowth

/-! # Actual two-sided pressure growth inside an HG2 selected prefix

Higher-pressure strata outside M_k do not enter either estimate. Only the
literal strata i<k other than the selected root j contribute; no subordinate
mixing, global spectral gap or recursive coordinate certificate is assumed.
-/
@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualPrefixSubordinateAggregates
open LeanShared ShiftedFiltrationGeometry FiltrationPressureConfinement ActualFiltrationGrowth
open ActualFiltrationIntervalGrowth ComplexStrongFeller RestrictedLayerChain
variable {X I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

private theorem power_norm_congr (C : AbsorbingMarkovChains.CanonicalChain X)
    (hSF : HasStrongFellerKernel C) (U V : Set X) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (h : U = V) (b : ℝ) (n : ℕ) :
    ‖(b • transferOperator (𝕜 := ℝ) (chain C U hU) (strongFeller C hSF U hU))^n‖ =
      ‖(b • transferOperator (𝕜 := ℝ) (chain C V hV) (strongFeller C hSF V hV))^n‖ := by
  subst V
  rfl

theorem exists_actual_prefix_two_subordinate_bounds
    (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (k : ℕ) (hkℓ : k ≤ ℓ) (j : Fin ℓ) (hjk : j.val < k)
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (b : ℝ) {β lam : ℝ} (hβ : 0 < β) (hβlam : β < lam)
    (hnoUp : ∀ i, 0 < i → i ≤ k → ∀ x ∈ levels T A Λ ℓ N D i,
      C.killedTransition x (levels T A Λ ℓ N D i)ᶜ = 0)
    (hleaf : ∀ i : Fin ℓ, i.val < k → i ≠ j → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      ‖(b • transferOperator (𝕜 := ℝ)
        (chain C (stratum T A Λ ℓ N D i)
          (stratum_measurable T A Λ ℓ N D hA i))
        (strongFeller C hSF (stratum T A Λ ℓ N D i)
          (stratum_measurable T A Λ ℓ N D hA i))) ^ n‖ ≤ B * β ^ n) :
    ∃ γ CA CD : ℝ, 0 < γ ∧ γ < lam ∧ 0 ≤ CA ∧ 0 ≤ CD ∧
      (∀ n : ℕ, ‖(b • transferOperator (𝕜 := ℝ)
        (chain C (levels T A Λ ℓ N D j.val \ A)
          ((ambient_levels_measurable T A hA Λ ℓ N D j.val).diff hA.measurableSet))
        (strongFeller C hSF (levels T A Λ ℓ N D j.val \ A)
          ((ambient_levels_measurable T A hA Λ ℓ N D j.val).diff hA.measurableSet)))^n‖ ≤ CA * γ^n) ∧
      (∀ n : ℕ, ‖(b • transferOperator (𝕜 := ℝ)
        (chain C (levels T A Λ ℓ N D k \ levels T A Λ ℓ N D (j.val + 1))
          ((ambient_levels_measurable T A hA Λ ℓ N D k).diff
            (ambient_levels_measurable T A hA Λ ℓ N D (j.val + 1))))
        (strongFeller C hSF (levels T A Λ ℓ N D k \ levels T A Λ ℓ N D (j.val + 1))
          ((ambient_levels_measurable T A hA Λ ℓ N D k).diff
            (ambient_levels_measurable T A hA Λ ℓ N D (j.val + 1)))))^n‖ ≤ CD * γ^n) := by
  obtain ⟨γ, hβγ, hγlam⟩ := exists_between hβlam
  obtain ⟨CA, hCA, hpowA⟩ := exists_actual_interval_power_bound T A hA Λ ℓ N D C hSF
    0 j.val (by omega) b hβ hβγ (fun i hi hik => hnoUp i hi (by omega)) (by
      intro i
      have hi := i.isLt
      exact hleaf ⟨0 + i.val, by omega⟩ (by change 0 + i.val < k; omega)
        (by intro he; have hv := congrArg Fin.val he; change 0 + i.val = j.val at hv; simp only [zero_add] at hv; omega))
  let r := j.val + 1
  let q := k - r
  obtain ⟨CD, hCD, hpowD⟩ := exists_actual_interval_power_bound T A hA Λ ℓ N D C hSF
    r q (by dsimp [r,q]; omega) b hβ hβγ
    (fun i hi hik => hnoUp i hi (by dsimp [r,q] at *; omega)) (by
      intro i
      have hi := i.isLt
      exact hleaf ⟨r + i.val, by dsimp [r,q] at *; omega⟩ (by change r + i.val < k; dsimp [r,q] at *; omega)
        (by intro he; have hv := congrArg Fin.val he; change r + i.val = j.val at hv; dsimp [r] at hv; omega))
  refine ⟨γ, CA, CD, hβ.trans hβγ, hγlam, hCA, hCD, ?_, ?_⟩
  · intro n
    have hset : levels T A Λ ℓ N D (0 + j.val) \ levels T A Λ ℓ N D 0 =
        levels T A Λ ℓ N D j.val \ A := by rw [zero_add, levels_zero]
    have he := power_norm_congr C hSF _ _
      ((ambient_levels_measurable T A hA Λ ℓ N D (0 + j.val)).diff
        (ambient_levels_measurable T A hA Λ ℓ N D 0))
      ((ambient_levels_measurable T A hA Λ ℓ N D j.val).diff hA.measurableSet) hset b n
    exact he.symm.trans_le (hpowA n)
  · intro n
    have hset : levels T A Λ ℓ N D (r + q) \ levels T A Λ ℓ N D r =
        levels T A Λ ℓ N D k \ levels T A Λ ℓ N D (j.val + 1) := by
      have he : r + q = k := by dsimp [r,q]; omega
      rw [he]
    have he := power_norm_congr C hSF _ _
      ((ambient_levels_measurable T A hA Λ ℓ N D (r + q)).diff
        (ambient_levels_measurable T A hA Λ ℓ N D r))
      ((ambient_levels_measurable T A hA Λ ℓ N D k).diff
        (ambient_levels_measurable T A hA Λ ℓ N D (j.val + 1))) hset b n
    exact he.symm.trans_le (hpowD n)

end ConditionedStochasticStabilityHyperbolic.Global.ActualPrefixSubordinateAggregates
