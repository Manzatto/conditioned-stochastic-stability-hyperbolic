module

public import LeanShared.Dynamics.RobustFiltration
public import ConditionedStochasticStabilityHyperbolic.Restriction.NoiseTransient

/-!
# Actual killed-noise transitions preserve positive filtration levels

The absorbing region is fixed: transition into it sends the path to the
cemetery. No robustness assumption on the raw map inside that region is
needed. The conclusions concern actual measurable kernel/path support; they
do not construct continuous block coordinates or prove a global limit theorem.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace ConditionedStochasticStabilityHyperbolic.Global

open AbsorbingMarkovChains ConditionedStochasticStabilityHyperbolic.Restriction

section Support

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- A positive level preserved by every random map has no live upward
transition in the actual weighted absorbing chain. -/
theorem noise_chain_no_upward_transition (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (F : X × Ω → X) (hF : Measurable F) (A : Set X) (hA : MeasurableSet A)
    (w : X → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W)
    (M : Set X) (hM : MeasurableSet M)
    (hmap : ∀ ω, MapsTo (fun x => F (x, ω)) M M) :
    ∀ x ∈ M, (NoiseKernel.chain ρ F hF Aᶜ hA.compl w hw W hW hwW).killedTransition x Mᶜ = 0 := by
  have hR : MeasurableSet {p : X × X | p.1 ∈ M → p.2 ∈ M} :=
    MeasurableSet.imp (hM.preimage measurable_fst) (hM.preimage measurable_snd)
  have hs := noise_chain_support ρ F hF Aᶜ hA.compl w hw W hW hwW _ hR
    (fun x ω _hx => fun hx => hmap ω hx)
  intro x hx
  apply measure_eq_zero_iff_ae_notMem.2
  filter_upwards [hs x] with y hy
  exact fun hbad => hbad (hy hx)

/-- Measurable level support holds at every consecutive live observation. -/
theorem ae_no_upward_step (C : CanonicalChain X) (M : Set X) (hM : MeasurableSet M)
    (hsupport : ∀ u, ∀ᵐ v ∂C.killedTransition u, u ∈ M → v ∈ M) (x : X) (n : ℕ) :
    ∀ᵐ ω ∂C.pathMeasure x, ω n ∈ Option.some '' M → ω (n + 1) ≠ none →
      ω (n + 1) ∈ Option.some '' M := by
  have hR : MeasurableSet {p : X × X | p.1 ∈ M → p.2 ∈ M} :=
    MeasurableSet.imp (hM.preimage measurable_fst) (hM.preimage measurable_snd)
  have hs := ae_live_transition_relation C _ hR hsupport x n
  filter_upwards [hs] with ω hω
  rintro ⟨u, hu, he⟩ halive
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp halive
  exact ⟨v, hω u v he.symm hv hu, hv.symm⟩

/-- Once a surviving canonical path enters a positive filtration level, it
cannot later leave that level while remaining alive. -/
theorem ae_no_upward_path (C : CanonicalChain X) (M : Set X) (hM : MeasurableSet M)
    (hsupport : ∀ u, ∀ᵐ v ∂C.killedTransition u, u ∈ M → v ∈ M) (x : X) :
    ∀ᵐ ω ∂C.pathMeasure x, ∀ m n : ℕ, m ≤ n → ω m ∈ Option.some '' M →
      ω n ≠ none → ω n ∈ Option.some '' M := by
  have hs : ∀ᵐ ω ∂C.pathMeasure x, ∀ n, ω n ∈ Option.some '' M →
      ω (n + 1) ≠ none → ω (n + 1) ∈ Option.some '' M :=
    ae_all_iff.2 (fun n => ae_no_upward_step C M hM hsupport x n)
  filter_upwards [hs, C.ae_absorbing x] with ω hstep habs
  intro m n hmn hm
  induction n, hmn using Nat.le_induction with
  | base => exact fun _ => hm
  | succ n hmn ih =>
      intro halive
      have hprev : ω n ≠ none := fun hn => halive (habs n (n + 1) (Nat.le_succ n) hn)
      exact hstep n (ih hprev) halive

end Support

section NoiseThreshold

variable {X Ω : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Ω]

/-- One positive threshold eliminates all upward live transitions across the
finite positive filtration levels. Level zero is exactly the fixed absorbing
region and does not require an adapted or robustness condition. -/
theorem exists_small_noise_no_upward_filtration
    (T : X ≃ₜ X) (N : ℕ) (A : Set X) (hA : MeasurableSet A)
    (M : ℕ → Set X) (ℓ : ℕ)
    (hcompact : ∀ i, 0 < i → i ≤ ℓ → IsCompact (M i))
    (hadapt : ∀ i, 0 < i → i ≤ ℓ → MapsTo T (M i) (interior (M i)))
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (F : ℝ → X × Ω → X) (hF : ∀ ε, Measurable (F ε))
    (w : X → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W)
    {C : ℝ} (hC : 0 ≤ C)
    (hnoise : ∀ ε > 0, ∀ ω, ∀ i, 0 < i → i ≤ ℓ →
      ∀ x ∈ LeanShared.shiftedFiltration T N A M i,
        dist (F ε (x, ω)) (T x) ≤ C * ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ i, 0 < i → i ≤ ℓ → ∀ x ∈ LeanShared.shiftedFiltration T N A M i,
        (NoiseKernel.chain ρ (F ε) (hF ε) Aᶜ hA.compl w hw W hW hwW).killedTransition x
          (LeanShared.shiftedFiltration T N A M i)ᶜ = 0 := by
  obtain ⟨ε₀, hε₀, hpreserve⟩ := LeanShared.exists_small_noise_shiftedFiltration_invariance
    T N A M ℓ hcompact hadapt (fun _ => Ω) (fun ε ω x => F ε (x, ω)) hC hnoise
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hsmall i hi hiℓ
  have hMi : IsCompact (LeanShared.shiftedFiltration T N A M i) := by
    rw [LeanShared.shiftedFiltration_pos T N A M hi]
    exact LeanShared.isCompact_preimage_iterate T (hcompact i hi hiℓ) N
  apply noise_chain_no_upward_transition ρ (F ε) (hF ε) A hA w hw W hW hwW _
    hMi.isClosed.measurableSet
  intro ω x hx
  exact interior_subset (hpreserve ε hε hsmall ω i hi hiℓ hx)

end NoiseThreshold

end ConditionedStochasticStabilityHyperbolic.Global
