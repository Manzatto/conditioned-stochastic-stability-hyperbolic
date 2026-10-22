module

public import LeanShared.Analysis.DomainPressureRefinement
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.CylinderAnnealedEstimates

/-!
# Strict closed-cylinder blocks from the source open-cover pressure

Baladi--Tsujii (2008), (3.2) and Lemma 3.5 supply the scalar root
asymptotic of the minimum finite open-cylinder cover cost. This theorem
selects the block length and the open subcover, then shrinks it to compact
outer cylinders and an open inner cover without increasing the principal
coefficient. No pressure asymptotic for arbitrary closed cylinders, nor
existence of a minimizing cover, is assumed.

Global continuity of the scalar density is not required. Boundedness on
each valid open cylinder suffices; continuity on valid compact outer closures
produces it via `domainValues_bddAbove_of_valid_closure`.

The scalar density must still be identified with the source pressure
density, including the positive-envelope distortion comparison (5.8).
The cover's inner persistence and moving closed-supremum robustness are
proved separately in `CylinderPrincipalCoefficient`.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace ConditionedStochasticStabilityHyperbolic.DomainPressureStrictBlock

open LeanShared.PressureCoverRefinement LeanShared.DomainPressureRefinement
open CylinderAnnealedEstimates

theorem exists_strict_refined_block {X : Type*} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] {I : ℕ → Type*}
    (K : Set X)
    (S : ℕ → Set X) (hS : ∀ N, IsCompact (S N))
    (u : (N : ℕ) → I N → Set X) (hu : ∀ N i, IsOpen (u N i))
    (hcover : ∀ N, ∃ c : Finset (I N), S N ⊆ ⋃ i ∈ c, u N i)
    (f : ℕ → X → ℝ)
    (hb : ∀ N i, BddAbove ({0} ∪ (f N) '' (K ∩ u N i)))
    (Q C ρ : ℝ) (hC : 0 < C) (hQρ : Q < ρ)
    (hpressure : Tendsto (fun N =>
      (coverCoefficient K (S N) (u N) (f N)) ^ ((N : ℝ)⁻¹)) atTop (𝓝 Q)) :
    ∃ N : ℕ, 0 < N ∧ ∃ (c : Finset (I N)) (v : c → Set X),
      S N ⊆ ⋃ i, v i ∧ (∀ i, IsOpen (v i)) ∧
      (∀ i, IsCompact (closure (v i))) ∧
      (∀ i, closure (v i) ⊆ u N i) ∧
      C * (∑ i, domainCoefficient K (closure (v i)) (f N)) < ρ ^ N := by
  have hq : ∀ N, 0 ≤ coverCoefficient K (S N) (u N) (f N) :=
    fun N => coverCoefficient_nonneg_of_bdd (hb N) (hcover N)
  obtain ⟨N, hN, hstrict⟩ := exists_strict_block _ hq Q C ρ hC.le hQρ hpressure
  have hstrict' : coverCoefficient K (S N) (u N) (f N) < ρ ^ N / C :=
    (lt_div_iff₀ hC).mpr (by simpa only [mul_comm] using hstrict)
  obtain ⟨c, v, hvc, hvo, hvk, hvs, hcost⟩ :=
    exists_refined_pressure_cover_of_bdd (hS N) (u N) (hu N) (hb N) (hcover N) hstrict'
  refine ⟨N, hN, c, v, hvc, hvo, hvk, hvs, ?_⟩
  simpa only [mul_comm] using (lt_div_iff₀ hC).mp hcost

end ConditionedStochasticStabilityHyperbolic.DomainPressureStrictBlock
