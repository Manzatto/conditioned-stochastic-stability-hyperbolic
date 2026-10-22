module

public import ConditionedStochasticStabilityHyperbolic.Neighborhoods.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Small-noise nonreturn and stable/unstable separation

The noise index type may depend on its intensity. Only a uniform `C * ε`
distance bound is needed; no probability law is used.
-/

@[expose] public section

open Set Metric

namespace ConditionedStochasticStabilityHyperbolic

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- The stable/unstable separation following Lemma `lem:set_U_stoch`. -/
theorem exists_stable_unstable_separation (T : X ≃ₜ X) {V Λ U : Set X}
    (hcore : LeanShared.isolatedCore T (closure V) = Λ)
    (hU : IsOpen U) (hΛU : Λ ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧
      thickening δ (LeanShared.forwardTrapped T (closure V)) ∩
        thickening δ (LeanShared.forwardTrapped T.symm (closure V)) ⊆ U := by
  apply LeanShared.exists_thickening_inter_subset_open
    (LeanShared.isClosed_forwardTrapped T.continuous isClosed_closure)
    (LeanShared.isClosed_forwardTrapped T.symm.continuous isClosed_closure) hU
  change LeanShared.isolatedCore T (closure V) ⊆ U
  rwa [hcore]

/-- Both separation properties hold at a common radius, uniformly for all
noise parameters of every sufficiently small positive intensity.

This packages Lemmas `lem:set_U`, `lem:set_U_stoch`, and the subsequent
stable/unstable separation statement. -/
theorem exists_small_noise_neighborhood (T : X ≃ₜ X) {V Λ : Set X}
    (hΛ : Λ.Nonempty) (hcore : LeanShared.isolatedCore T (closure V) = Λ)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : closure (thickening ρ Λ) ⊆ V)
    {Ω : ℝ → Type*} (F : (ε : ℝ) → Ω ε → X → X)
    {C : ℝ} (hC : 0 < C)
    (hclose : ∀ ε, 0 < ε → ∀ ω : Ω ε, ∀ x ∈ closure V,
      dist (F ε ω x) (T x) ≤ C * ε) :
    ∃ N : ℕ, 0 < N ∧
      IsOpen (orbitNeighborhood T Λ ρ N) ∧
      Λ ⊆ orbitNeighborhood T Λ ρ N ∧
      closure (orbitNeighborhood T Λ ρ N) ⊆ V ∧
      (T '' closure (orbitNeighborhood T Λ ρ N)) ∩
        LeanShared.forwardTrapped T (closure V) ⊆ orbitNeighborhood T Λ ρ N ∧
      ∃ δ ε₀ : ℝ, 0 < δ ∧ 0 < ε₀ ∧
        (thickening δ (LeanShared.forwardTrapped T (closure V)) ∩
          thickening δ (LeanShared.forwardTrapped T.symm (closure V)) ⊆
            orbitNeighborhood T Λ ρ N) ∧
        ∀ ε, 0 < ε → ε < ε₀ → ∀ ω : Ω ε,
          ∀ x ∈ closure (orbitNeighborhood T Λ ρ N),
            F ε ω x ∉ thickening δ (LeanShared.forwardTrapped T (closure V)) \
              orbitNeighborhood T Λ ρ N := by
  obtain ⟨N, hN, hU, hΛU, hUV, hsep⟩ := exists_orbitNeighborhood T hΛ hcore hρ hball
  obtain ⟨δ₁, hδ₁, hnonreturn⟩ := LeanShared.exists_uniform_nonreturn T.continuous
    isClosed_closure.isCompact
    (LeanShared.isClosed_forwardTrapped T.continuous isClosed_closure) hU hsep
  obtain ⟨δ₂, hδ₂, hstable⟩ := exists_stable_unstable_separation T hcore hU hΛU
  refine ⟨N, hN, hU, hΛU, hUV, hsep, min δ₁ δ₂, δ₁ / C,
    lt_min hδ₁ hδ₂, div_pos hδ₁ hC, ?_, ?_⟩
  · exact (inter_subset_inter (thickening_mono (min_le_right _ _) _)
      (thickening_mono (min_le_right _ _) _)).trans hstable
  · intro ε hε hε₀ ω x hx hbad
    have hF : ∀ y ∈ closure (orbitNeighborhood T Λ ρ N),
        dist (F ε ω y) (T y) < δ₁ := by
      intro y hy
      have hbound := hclose ε hε ω y (subset_closure (hUV hy))
      have hsmall := (lt_div_iff₀ hC).mp hε₀
      nlinarith
    apply hnonreturn (F ε ω) hF x hx
    exact ⟨thickening_mono (min_le_left _ _) _ hbad.1, hbad.2⟩

end ConditionedStochasticStabilityHyperbolic
