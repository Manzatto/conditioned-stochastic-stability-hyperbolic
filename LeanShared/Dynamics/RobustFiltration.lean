module

public import LeanShared.Dynamics.ShiftedFiltration
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith

/-!
# One common perturbation threshold for finitely many positive levels

Compact adapted positive levels have a common positive margin. The absorbing
level remains fixed and has no robustness or compactness assumption here;
the stochastic process kills on entering that level.
-/

@[expose] public section

open Set Finset Metric

namespace LeanShared

variable {X J : Type*} [MetricSpace X] [Fintype J]

/-- A finite family of compact adapted regions has one common map tolerance,
including the empty-family case. -/
theorem exists_pos_finite_adapted_margin (T : X → X) (hT : Continuous T)
    (M : J → Set X) (hcompact : ∀ j, IsCompact (M j))
    (hadapt : ∀ j, MapsTo T (M j) (interior (M j))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ F : X → X,
      (∀ j, ∀ x ∈ M j, dist (F x) (T x) < δ) →
      ∀ j, MapsTo F (M j) (interior (M j)) := by
  classical
  by_cases hne : (univ : Finset J).Nonempty
  · have hmargin (j : J) : ∃ δ : ℝ, 0 < δ ∧ ∀ F : X → X,
        (∀ x ∈ M j, dist (F x) (T x) < δ) → MapsTo F (M j) (interior (M j)) := by
      obtain ⟨δ, hδ, hthick⟩ := ((hcompact j).image hT).exists_thickening_subset_open
        isOpen_interior (hadapt j).image_subset
      refine ⟨δ, hδ, ?_⟩
      intro F hF x hx
      exact hthick (Metric.mem_thickening_iff.mpr ⟨T x, ⟨x, hx, rfl⟩, hF x hx⟩)
    choose d hd hmap using hmargin
    let δ : ℝ := univ.inf' hne d
    have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 (fun j _ => hd j)
    refine ⟨δ, hδ, ?_⟩
    intro F hF j
    apply hmap j F
    intro x hx
    exact (hF j x hx).trans_le (Finset.inf'_le _ (mem_univ j))
  · refine ⟨1, zero_lt_one, ?_⟩
    intro _F _hF j
    exact (hne ⟨j, mem_univ j⟩).elim

/-- A uniform `C * epsilon` bound gives one noise threshold preserving every
positive level in the finite family. Noise types may depend on intensity. -/
theorem exists_small_noise_finite_adapted_invariance (T : X → X) (hT : Continuous T)
    (M : J → Set X) (hcompact : ∀ j, IsCompact (M j))
    (hadapt : ∀ j, MapsTo T (M j) (interior (M j)))
    (Ω : ℝ → Type*) (F : (ε : ℝ) → Ω ε → X → X)
    {C : ℝ} (hC : 0 ≤ C)
    (hnoise : ∀ ε > 0, ∀ ω : Ω ε, ∀ j, ∀ x ∈ M j,
      dist (F ε ω x) (T x) ≤ C * ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ → ∀ ω : Ω ε,
      ∀ j, MapsTo (F ε ω) (M j) (interior (M j)) := by
  obtain ⟨δ, hδ, hpreserve⟩ := exists_pos_finite_adapted_margin T hT M hcompact hadapt
  have hC1 : 0 < C + 1 := by linarith
  refine ⟨δ / (C + 1), div_pos hδ hC1, ?_⟩
  intro ε hε hsmall ω
  apply hpreserve (F ε ω)
  intro j x hx
  have hprod : ε * (C + 1) < δ := (lt_div_iff₀ hC1).mp hsmall
  have hbound := hnoise ε hε ω j x hx
  nlinarith

/-- For a shifted finite filtration all positive levels share one threshold;
the fixed absorption level `A` requires no separate map robustness. -/
theorem exists_small_noise_shiftedFiltration_invariance
    (T : X ≃ₜ X) (N : ℕ) (A : Set X) (M : ℕ → Set X) (ℓ : ℕ)
    (hcompact : ∀ i, 0 < i → i ≤ ℓ → IsCompact (M i))
    (hadapt : ∀ i, 0 < i → i ≤ ℓ → MapsTo T (M i) (interior (M i)))
    (Ω : ℝ → Type*) (F : (ε : ℝ) → Ω ε → X → X)
    {C : ℝ} (hC : 0 ≤ C)
    (hnoise : ∀ ε > 0, ∀ ω : Ω ε, ∀ i, 0 < i → i ≤ ℓ →
      ∀ x ∈ shiftedFiltration T N A M i, dist (F ε ω x) (T x) ≤ C * ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ → ∀ ω : Ω ε,
      ∀ i, 0 < i → i ≤ ℓ → MapsTo (F ε ω) (shiftedFiltration T N A M i)
        (interior (shiftedFiltration T N A M i)) := by
  obtain ⟨ε₀, hε₀, hpreserve⟩ := exists_small_noise_finite_adapted_invariance
    (T : X → X) T.continuous
    (fun j : Fin ℓ => shiftedFiltration T N A M (j.val + 1))
    (fun j => by
      rw [shiftedFiltration_pos T N A M (by omega : 0 < j.val + 1)]
      exact isCompact_preimage_iterate T (hcompact _ (by omega) (by omega)) N)
    (fun j => by
      rw [shiftedFiltration_pos T N A M (by omega : 0 < j.val + 1)]
      intro x hx
      apply preimage_interior_subset_interior_preimage (T.continuous.iterate N)
      change (T : X → X)^[N] (T x) ∈ interior (M (j.val + 1))
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      exact hadapt _ (by omega) (by omega) hx)
    Ω F hC (fun ε hε ω j x hx => hnoise ε hε ω _ (by omega) (by omega) x hx)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hsmall ω i hi hiℓ
  let j : Fin ℓ := ⟨i - 1, by omega⟩
  have heq : j.val + 1 = i := by dsimp [j]; omega
  simpa only [heq] using hpreserve ε hε hsmall ω j

end LeanShared
