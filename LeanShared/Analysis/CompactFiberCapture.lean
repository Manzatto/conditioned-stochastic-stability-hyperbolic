module

public import LeanShared.Analysis.CylinderPrincipalCoefficient

/-! A fixed open partition-capture region containing deterministic
survivors also captures all nearby surviving fibers. The region and its
smooth partition are chosen before the random word. Only compactness and
the actual closed moving relation are needed for this robustness step. -/

public noncomputable section
open Set
namespace LeanShared.CompactFiberCapture
open CylinderPrincipalCoefficient
variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]

theorem exists_open_capture (K : Set X) (hK : IsCompact K)
    (R : Set (P × X)) (hR : IsClosed R) (p : P)
    (capture : Set X) (hc : IsOpen capture) (href : fiber K R p ⊆ capture) :
    ∃ U : Set P, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U, fiber K R q ⊆ capture := by
  have hsub : ({p} : Set P) ×ˢ K ⊆ Rᶜ ∪ (univ ×ˢ capture) := by
    rintro ⟨q, x⟩ ⟨hq, hx⟩
    have hqp : q = p := mem_singleton_iff.mp hq
    subst q
    by_cases hr : (p, x) ∈ R
    · exact Or.inr ⟨mem_univ _, href ⟨hx, hr⟩⟩
    · exact Or.inl hr
  obtain ⟨U, W, hU, _, hpU, hKW, hUW⟩ := generalized_tube_lemma
    isCompact_singleton hK (hR.isOpen_compl.union (isOpen_univ.prod hc)) hsub
  refine ⟨U, hU, singleton_subset_iff.mp hpU, ?_⟩
  intro q hq x hx
  exact ((hUW ⟨hq, hKW hx.1⟩).resolve_left (not_not.mpr hx.2)).2

end LeanShared.CompactFiberCapture
