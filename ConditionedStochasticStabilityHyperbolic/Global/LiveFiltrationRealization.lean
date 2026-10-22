module

public import ConditionedStochasticStabilityHyperbolic.Global.ShiftedFiltrationGeometry
public import ConditionedStochasticStabilityHyperbolic.Global.RestrictedLayerChain

/-!
# Augmented filtration on the literal live state space

Ambient level zero is the fixed open absorbing A. On the actual live subtype
A^c its pullback is empty, as required by the finite-layer induction. Actual
no-upward kernel support pulls back to every positive live prefix without
assuming random invariance of A or an invertible map on the live subtype.
All closed analytic layers are proved contained in A^c.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace ConditionedStochasticStabilityHyperbolic.Global.LiveFiltrationRealization
open LeanShared FiltrationLayerGeometry ShiftedFiltrationGeometry RestrictedLayerChain
variable {X I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ N : ℕ)
  (D : AdaptedSource T A Λ ℓ)

/-- Pullback of a positive ambient level to the literal live-state type. -/
def liveLevels (i : ℕ) : Set (Aᶜ : Set X) :=
  Subtype.val ⁻¹' levels T A Λ ℓ N D i

omit [MeasurableSpace X] [BorelSpace X] in
/-- The absorbing zero level is empty on the actual live-state type. -/
theorem liveLevels_zero : liveLevels T A Λ ℓ N D 0 = ∅ := by
  ext x
  change (x.val ∈ levels T A Λ ℓ N D 0) ↔ False
  rw [levels_zero]
  exact ⟨fun h => x.property h, False.elim⟩

omit [MeasurableSpace X] [BorelSpace X] in
theorem liveLevels_monotone : Monotone (liveLevels T A Λ ℓ N D) := by
  intro i j hij x hx
  exact levels_monotone T A Λ ℓ N D hij hx

/-- Positive live levels are measurable; the absorbing boundary has no
regularity or nullity premise. -/
theorem liveLevels_measurable (i : ℕ) (hiℓ : i ≤ ℓ) :
    MeasurableSet (liveLevels T A Λ ℓ N D i) := by
  by_cases hi : i = 0
  · rw [hi, liveLevels_zero]
    exact MeasurableSet.empty
  · exact (levels_positive_compact T A Λ ℓ N D i (Nat.pos_of_ne_zero hi) hiℓ).isClosed.measurableSet.preimage
      measurable_subtype_coe

omit [MeasurableSpace X] [BorelSpace X] in
/-- Literal live strips are precisely the pullbacks of the actual ambient
strata; no boundary coordinate identification is assumed. -/
theorem live_stratum_eq (i : ℕ) :
    filtrationLayer (liveLevels T A Λ ℓ N D) i =
      Subtype.val ⁻¹' filtrationLayer (levels T A Λ ℓ N D) i := by
  rw [filtrationLayer, filtrationLayer, liveLevels, liveLevels, preimage_sdiff]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Closed analytic layers never intersect the absorbing open region,
including the first layer whose actual stratum is already closed. -/
theorem closed_layer_subset_live (hA : IsOpen A) (i : Fin ℓ) :
    closure (filtrationLayer (levels T A Λ ℓ N D) i.val) ⊆ Aᶜ := by
  by_cases hi : i.val = 0
  · have hclosed : IsClosed (filtrationLayer (levels T A Λ ℓ N D) i.val) := by
      rw [hi, filtrationLayer, zero_add, levels_zero]
      exact absorbing_stratum_closed _ A
        (levels_positive_compact T A Λ ℓ N D 1 (by omega) (by omega)).isClosed hA
    rw [hclosed.closure_eq, hi, filtrationLayer, zero_add, levels_zero]
    exact fun _ hx => hx.2
  · have hAlevel : A ⊆ levels T A Λ ℓ N D i.val := by
      have h := levels_monotone T A Λ ℓ N D (Nat.zero_le i.val)
      simpa only [levels_zero] using h
    have hAint : A ⊆ interior (levels T A Λ ℓ N D i.val) := interior_maximal hAlevel hA
    intro x hx hxA
    have hs := closure_stratum_subset _ _
      (levels_positive_compact T A Λ ℓ N D (i.val + 1) (by omega) (by omega)).isClosed hx
    exact hs.2 (hAint hxA)

omit T Λ ℓ N D [MetricSpace X] [BorelSpace X] in
/-- Actual ambient prefix support becomes exact support for the real chain
on A^c. No statement about noise maps starting in A is needed. -/
theorem live_prefix_kernel_support
    (C : AbsorbingMarkovChains.CanonicalChain X) (hA : MeasurableSet A)
    (M : Set X) (hM : MeasurableSet M)
    (hsupport : ∀ x ∈ M, C.killedTransition x Mᶜ = 0) :
    ∀ x : (Aᶜ : Set X), x ∈ Subtype.val ⁻¹' M →
      (chain C Aᶜ hA.compl).killedTransition x (Subtype.val ⁻¹' M)ᶜ = 0 := by
  intro x hx
  rw [RestrictedLayerChain.killedTransition,
    LeanShared.SubtypeKernel.restrict_apply_set _ Aᶜ hA.compl x _
      (hM.preimage measurable_subtype_coe).compl]
  apply le_antisymm _ bot_le
  calc
    _ ≤ C.killedTransition x.val Mᶜ := measure_mono (by
      rintro y ⟨z, hz, rfl⟩
      exact hz)
    _ = 0 := hsupport x.val hx

end ConditionedStochasticStabilityHyperbolic.Global.LiveFiltrationRealization
