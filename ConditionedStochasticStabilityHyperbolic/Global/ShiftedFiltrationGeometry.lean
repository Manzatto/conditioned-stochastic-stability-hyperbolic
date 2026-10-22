module

public import ConditionedStochasticStabilityHyperbolic.Global.FiltrationLayerGeometry
public import ConditionedStochasticStabilityHyperbolic.Global.FiltrationKernel

/-!
# Shifted adapted-filtration geometry supplies actual global layer data

The cited classical source specifies positive compact adapted levels and the
literal maximal invariant basic sets. Interior isolation and equality with
closed-layer cores are derived. The absorbing zero level remains A, and its
boundary is not assumed null. A common actual noise threshold supplies all
prefix-kernel support statements.
-/

@[expose] public noncomputable section
open Set Function MeasureTheory ProbabilityTheory
namespace ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationGeometry
open LeanShared FiltrationLayerGeometry
variable {X I : Type*} [MetricSpace X]

/-- Classical adapted-filtration source, for a chosen compatible enumeration.
Smooth boundaries and their nullity are recorded separately below. -/
structure AdaptedSource (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ : ℕ) where
  levels : ℕ → Set X
  index : Fin ℓ → I
  zero : levels 0 = A
  monotone : Monotone levels
  absorbing_forward : MapsTo T A A
  compact_positive : ∀ i, 0 < i → i ≤ ℓ → IsCompact (levels i)
  adapted_positive : ∀ i, 0 < i → i ≤ ℓ → MapsTo T (levels i) (interior (levels i))
  terminal : levels ℓ = univ
  literal_core : ∀ i : Fin ℓ, isolatedCore T (filtrationLayer levels i.val) = Λ (index i)

variable (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ N : ℕ)
  (D : AdaptedSource T A Λ ℓ)

def levels : ℕ → Set X := shiftedFiltration T N A D.levels

theorem levels_zero : levels T A Λ ℓ N D 0 = A := shiftedFiltration_zero _ _ _ _

theorem levels_monotone : Monotone (levels T A Λ ℓ N D) := by
  apply shiftedFiltration_monotone T N A D.levels D.monotone _ D.absorbing_forward
  intro x hx
  exact D.monotone (Nat.zero_le 1) (D.zero.symm ▸ hx)

theorem levels_positive_compact (i : ℕ) (hi : 0 < i) (hiℓ : i ≤ ℓ) :
    IsCompact (levels T A Λ ℓ N D i) := by
  rw [levels, shiftedFiltration_pos T N A D.levels hi]
  exact isCompact_preimage_iterate T (D.compact_positive i hi hiℓ) N

theorem levels_positive_adapted (i : ℕ) (hi : 0 < i) (hiℓ : i ≤ ℓ) :
    MapsTo T (levels T A Λ ℓ N D i) (interior (levels T A Λ ℓ N D i)) := by
  rw [levels, shiftedFiltration_pos T N A D.levels hi]
  intro x hx
  apply preimage_interior_subset_interior_preimage (T.continuous.iterate N)
  change (T : X → X)^[N] (T x) ∈ interior (D.levels i)
  rw [← iterate_succ_apply, iterate_succ_apply']
  exact D.adapted_positive i hi hiℓ hx

/-- The common preimage shift does not change any literal stratum core. -/
theorem literal_core (i : Fin ℓ) :
    isolatedCore T (filtrationLayer (levels T A Λ ℓ N D) i.val) = Λ (D.index i) := by
  rw [levels, isolatedCore_shiftedFiltration_layer]
  have hzero : shiftedFiltration T 0 A D.levels = D.levels := by
    funext j
    by_cases hj : j = 0
    · subst j
      rw [shiftedFiltration_zero, D.zero]
    · rw [shiftedFiltration_pos T 0 A D.levels (Nat.pos_of_ne_zero hj)]
      rfl
  rw [hzero]
  exact D.literal_core i

/-- Closed analytic layers and literal Borel strata share exactly the
same basic set, including the absorbing first layer. -/
theorem closed_layer_core (hA : IsOpen A) (i : Fin ℓ) :
    isolatedCore T (closure (filtrationLayer (levels T A Λ ℓ N D) i.val)) = Λ (D.index i) := by
  by_cases hi : i.val = 0
  · have hclosed : IsClosed (filtrationLayer (levels T A Λ ℓ N D) i.val) := by
      rw [hi, filtrationLayer, zero_add, levels_zero]
      exact absorbing_stratum_closed _ A
        (levels_positive_compact T A Λ ℓ N D 1 (by omega) (by omega)).isClosed hA
    rw [hclosed.closure_eq]
    exact literal_core T A Λ ℓ N D i
  · rw [filtrationLayer, isolatedCore_closed_stratum_eq T _ _
      (levels_positive_compact T A Λ ℓ N D (i.val + 1) (by omega) (by omega)).isClosed
      (levels_positive_adapted T A Λ ℓ N D i.val (Nat.pos_of_ne_zero hi) (by omega))]
    exact literal_core T A Λ ℓ N D i

/-- The explicit retained-basic-set separation is needed only at absorbing
level zero; all positive-level interior properties follow from adaptedness. -/
theorem basic_set_interior_stratum
    (hsep : ∀ j, Λ j ⊆ interior Aᶜ) (i : Fin ℓ) :
    Λ (D.index i) ⊆ interior (filtrationLayer (levels T A Λ ℓ N D) i.val) := by
  by_cases hi : i.val = 0
  · rw [hi, filtrationLayer, zero_add, levels_zero]
    apply absorbing_core_subset_interior T (levels T A Λ ℓ N D 1) A (Λ (D.index i))
      (levels_positive_adapted T A Λ ℓ N D 1 (by omega) (by omega))
      _ (hsep _)
    simpa only [hi, filtrationLayer, zero_add, levels_zero] using literal_core T A Λ ℓ N D i
  · rw [← literal_core T A Λ ℓ N D i, filtrationLayer]
    exact isolatedCore_subset_interior_stratum T _ _
      (levels_positive_compact T A Λ ℓ N D i.val (Nat.pos_of_ne_zero hi) (by omega)).isClosed
      (levels_positive_adapted T A Λ ℓ N D (i.val + 1) (by omega) (by omega))

section Noise
variable [MeasurableSpace X] [BorelSpace X] {Ω : Type*} [MeasurableSpace Ω]

/-- Every positive shifted level is a genuinely invariant prefix for the
actual fixed-A noisy chain, with one common threshold for all prefixes. -/
theorem exists_common_actual_prefix_support
    (hA : MeasurableSet A) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (F : ℝ → X × Ω → X) (hF : ∀ ε, Measurable (F ε))
    (w : X → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W)
    {c : ℝ} (hc : 0 ≤ c)
    (hnoise : ∀ ε > 0, ∀ ω, ∀ i, 0 < i → i ≤ ℓ →
      ∀ x ∈ levels T A Λ ℓ N D i, dist (F ε (x, ω)) (T x) ≤ c * ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ → ∀ i, 0 < i → i ≤ ℓ →
      ∀ x ∈ levels T A Λ ℓ N D i,
        (NoiseKernel.chain ρ (F ε) (hF ε) Aᶜ hA.compl w hw W hW hwW).killedTransition x
          (levels T A Λ ℓ N D i)ᶜ = 0 := by
  exact exists_small_noise_no_upward_filtration T N A hA D.levels ℓ
    D.compact_positive D.adapted_positive ρ F hF w hw W hW hwW hc hnoise

end Noise
end ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationGeometry
