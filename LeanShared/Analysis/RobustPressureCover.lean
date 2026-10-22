module

public import LeanShared.Analysis.PressureCoverRefinement

/-!
# Persistence of the cover selected from the pressure coefficient

The deterministic infimum open-cover coefficient selects a compact
outer/open inner refinement. The actual closed moving-survival relation
then supplies one parameter neighborhood on which the inner cover still
covers every surviving initial point. This is a consequence of compactness,
not a supplied varying-word covering hypothesis.
-/

@[expose] public noncomputable section

open Set
open scoped BigOperators

namespace LeanShared.RobustPressureCover

open CylinderPrincipalCoefficient PressureCoverRefinement

theorem exists_robust_refined_cover {P X I : Type*}
    [TopologicalSpace P] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (K : Set X) (hK : IsCompact K) (R : Set (P × X)) (hR : IsClosed R)
    (p₀ : P) (f : X → ℝ) (hf : Continuous f)
    (u : I → Set X) (hu : ∀ i, IsOpen (u i))
    (hcover : ∃ c : Finset I, fiber K R p₀ ⊆ ⋃ i ∈ c, u i)
    (a : ℝ) (hstrict : coverCoefficient K (fiber K R p₀) u f < a) :
    ∃ (c : Finset I) (v : c → Set X) (W : Set P),
      IsOpen W ∧ p₀ ∈ W ∧
      (∀ p ∈ W, fiber K R p ⊆ ⋃ i, v i) ∧
      (∀ i, IsOpen (v i)) ∧ (∀ i, IsCompact (closure (v i))) ∧
      (∀ i, closure (v i) ⊆ u i) ∧
      (∑ i, domainCoefficient K (closure (v i)) f) < a := by
  obtain ⟨c, v, hvc, hvo, hvk, hvs, hcost⟩ :=
    exists_refined_pressure_cover hK (fiber_isCompact hK hR p₀) hf u hu hcover hstrict
  let O : Set (P × X) := Prod.snd ⁻¹' (⋃ i, v i)
  have hO : IsOpen O := (isOpen_iUnion hvo).preimage continuous_snd
  obtain ⟨W, hW, hpW, hrobust⟩ := exists_robust_subcover hK hR O hO p₀
    (fun x hx => hvc hx)
  exact ⟨c, v, W, hW, hpW, fun p hp x hx => hrobust p hp x hx,
    hvo, hvk, hvs, hcost⟩

end LeanShared.RobustPressureCover
