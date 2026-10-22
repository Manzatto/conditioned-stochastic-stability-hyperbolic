module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualFiltrationGrowth
public import ConditionedStochasticStabilityHyperbolic.Global.LiteralFiltrationGrowth

/-!
# Actual finite filtration interval growth with lower-level leakage

For G=M_(r+k) minus M_r, actual restricted interval chains allow departure
into lower M_r. Only relative no-upward support inside G is required. Ambient
stratum estimates and the proved adapted geometry produce all interval power
bounds, supplying subordinate upper aggregates around selected dominant roots.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualFiltrationIntervalGrowth
open LeanShared ShiftedFiltrationGeometry FiltrationPressureConfinement ActualFiltrationGrowth
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel RelativeFiltrationGrowth
variable {X I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

private theorem restricted_power_norm_congr
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (U V : Set X) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (heq : U = V) (b : ℝ) (n : ℕ) :
    ‖(b • transferOperator (𝕜 := ℝ) (chain C U hU) (strongFeller C hSF U hU)) ^ n‖ =
      ‖(b • transferOperator (𝕜 := ℝ) (chain C V hV) (strongFeller C hSF V hV)) ^ n‖ := by
  subst V
  rfl

/-- Actual consecutive strata bound the actual killed interval, even when
its paths can fall into lower levels. No subordinate mixing is required. -/
theorem exists_actual_interval_power_bound
    (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ)
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (r k : ℕ) (hrkℓ : r + k ≤ ℓ) (b : ℝ) {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ)
    (hnoUp : ∀ i, 0 < i → i ≤ r + k → ∀ x ∈ levels T A Λ ℓ N D i,
      C.killedTransition x (levels T A Λ ℓ N D i)ᶜ = 0)
    (hleaf : ∀ i : Fin k, ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      ‖(b • transferOperator (𝕜 := ℝ)
        (chain C (stratum T A Λ ℓ N D ⟨r + i.val, by omega⟩)
          (stratum_measurable T A Λ ℓ N D hA ⟨r + i.val, by omega⟩))
        (strongFeller C hSF (stratum T A Λ ℓ N D ⟨r + i.val, by omega⟩)
          (stratum_measurable T A Λ ℓ N D hA ⟨r + i.val, by omega⟩))) ^ n‖ ≤ B * β ^ n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      ‖(b • transferOperator (𝕜 := ℝ)
        (chain C (levels T A Λ ℓ N D (r + k) \ levels T A Λ ℓ N D r)
          ((ambient_levels_measurable T A hA Λ ℓ N D (r + k)).diff
            (ambient_levels_measurable T A hA Λ ℓ N D r)))
        (strongFeller C hSF (levels T A Λ ℓ N D (r + k) \ levels T A Λ ℓ N D r)
          ((ambient_levels_measurable T A hA Λ ℓ N D (r + k)).diff
            (ambient_levels_measurable T A hA Λ ℓ N D r)))) ^ n‖ ≤ B * γ ^ n := by
  let V := levels T A Λ ℓ N D
  let G := V (r + k) \ V r
  have hG : MeasurableSet G := (ambient_levels_measurable T A hA Λ ℓ N D (r + k)).diff
    (ambient_levels_measurable T A hA Λ ℓ N D r)
  let CG := chain C G hG
  let sfG := strongFeller C hSF G hG
  let M : ℕ → Set G := fun i => Subtype.val ⁻¹' V (r + i)
  have hM : ∀ i, MeasurableSet (M i) := fun i =>
    (ambient_levels_measurable T A hA Λ ℓ N D (r + i)).preimage measurable_subtype_coe
  have hzero : M 0 = ∅ := by
    ext x
    change (x.val ∈ V (r + 0)) ↔ False
    simp only [Nat.add_zero]
    exact ⟨fun hx => x.property.2 hx, False.elim⟩
  have hmon : ∀ i, M i ⊆ M (i + 1) := by
    intro i x hx
    exact levels_monotone T A Λ ℓ N D (Nat.add_le_add_left (Nat.le_succ i) r) hx
  obtain ⟨B, hB, hpow⟩ := exists_literal_filtration_power_bound CG sfG M hM hzero hmon b hβ k
    (by
      intro i hik x hx
      by_cases hi : i = 0
      · rw [hi, hzero] at hx
        exact hx.elim
      · have hs := LiteralFiltrationGrowth.restricted_level_support C (V (r + i)) G
          (ambient_levels_measurable T A hA Λ ℓ N D (r + i)) hG
          (hnoUp (r + i) (by omega) (by omega)) x hx
        have hz : CG.killedTransition x (M i)ᶜ = 0 := by
          change ∀ᵐ y ∂CG.killedTransition x, y ∈ M i at hs
          exact ae_iff.mp hs
        apply le_antisymm _ bot_le
        exact (measure_mono (fun _ h => h.2 : M k \ M i ⊆ (M i)ᶜ)).trans_eq hz)
    (by
      intro i hik
      let j : Fin k := ⟨i, hik⟩
      let t : Fin ℓ := ⟨r + i, by omega⟩
      obtain ⟨B, hB, hp⟩ := hleaf j
      refine ⟨B, hB, ?_⟩
      intro n
      have hsub : stratum T A Λ ℓ N D t ⊆ G := by
        intro x hx
        change x ∈ V (r + i + 1) \ V (r + i) at hx
        refine ⟨levels_monotone T A Λ ℓ N D (by omega) hx.1, ?_⟩
        intro hxlow
        exact hx.2 (levels_monotone T A Λ ℓ N D (by omega) hxlow)
      have he := nested_power_norm_eq (𝕜 := ℝ) (stratum T A Λ ℓ N D t) G hsub C hSF
        (stratum_measurable T A Λ ℓ N D hA t) hG b n
      exact he ▸ hp n) hβγ
  have hterminal : M k = innerLevel G G := by
    ext x
    change (x.val ∈ V (r + k)) ↔ x.val ∈ G
    exact ⟨fun _ => x.property, fun _ => x.property.1⟩
  refine ⟨B, hB, ?_⟩
  intro n
  have he1 := restricted_power_norm_congr CG sfG (M k) (innerLevel G G) (hM k)
    (hG.preimage measurable_subtype_coe) hterminal b n
  have he2 := nested_power_norm_eq (𝕜 := ℝ) G G Subset.rfl C hSF hG hG b n
  exact he2 ▸ he1 ▸ hpow n

end ConditionedStochasticStabilityHyperbolic.Global.ActualFiltrationIntervalGrowth
