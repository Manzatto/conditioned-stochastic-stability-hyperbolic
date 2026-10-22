module

public import LeanShared.Dynamics.PeriodicFiberSubsetMatchingExact
public import LeanShared.Dynamics.PeriodicMatchingFiberSubset

/-! Exact finite-order Manning correspondence: genuine periodic signed
matching walks over x are in bijection with invariant subsets of the
literal original return fiber of the same cardinality.  The bijection
preserves the restricted return sign exactly.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization
variable {A X : Type*} [MetricSpace X] [TopologicalSpace A] [Fintype A] [DecidableEq A]

@[expose] def PeriodicMatchingFiber (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (k : ℕ) (x : X) (period : ℕ) : Type _ :=
  {a : (matchingCode T rectangles code k) ⁻¹' {x} // Function.Periodic a.val.val (period : ℤ)}

theorem periodic_matching_subset_equivalence (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (properties : MarkovCodingProperties T rectangles code)
    (x : X) [DecidableEq (code ⁻¹' {x})] (period : ℕ) (positive : 0 < period)
    (fixed : (T : X → X)^[period] x = x)
    (P : Equiv.Perm (code ⁻¹' {x}))
    (returns : ∀ a, (P a).val = (shift (Transition T rectangles) : _ → _)^[period] a.val)
    (k : ℕ) :
    ∃ e : PeriodicMatchingFiber T rectangles code k x period ≃
      {s : Finset (code ⁻¹' {x}) // s.card = k + 1 ∧ ∀ p, P p ∈ s ↔ p ∈ s},
      ∀ a, (e a).val = matchingFiberSubset T rectangles code properties.geometry k x a.val ∧
        (∏ i ∈ Finset.range period, matchingEdgeSign (a.val.val.val i)) =
          Equiv.Perm.sign (P.subtypePerm (e a).property.2) := by
  classical
  let source := PeriodicMatchingFiber T rectangles code k x period
  let target := {s : Finset (code ⁻¹' {x}) // s.card = k + 1 ∧ ∀ p, P p ∈ s ↔ p ∈ s}
  have invariant (a : source) : ∀ p,
      P p ∈ matchingFiberSubset T rectangles code properties.geometry k x a.val ↔
      p ∈ matchingFiberSubset T rectangles code properties.geometry k x a.val :=
    (periodic_matching_fiber_subset T rectangles code properties k x period P returns a.val a.property).choose
  let f : source → target := fun a =>
    ⟨matchingFiberSubset T rectangles code properties.geometry k x a.val,
      matchingFiberSubset_card T rectangles code properties.geometry k x a.val, invariant a⟩
  have bijective : Bijective f := by
    constructor
    · intro a b equal
      apply Subtype.ext
      exact matchingFiberSubset_injective T rectangles code properties k x period positive fixed
        (congrArg (fun s : target => s.val) equal)
    · intro s
      obtain ⟨walk, inside, extracted, periodic, _sign⟩ :=
        periodic_fiber_subset_matching_exact T rectangles code properties x period positive fixed
          P returns s.val s.property.2 k s.property.1
      refine ⟨⟨⟨walk, inside⟩, periodic⟩, ?_⟩
      exact Subtype.ext extracted
  let e := Equiv.ofBijective f bijective
  refine ⟨e, fun a => ⟨rfl, ?_⟩⟩
  exact (periodic_matching_fiber_subset T rectangles code properties k x period P returns a.val a.property).choose_spec

end LeanShared.BilateralShadowingCoding
