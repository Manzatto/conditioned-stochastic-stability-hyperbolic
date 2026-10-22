module

public import LeanShared.Dynamics.FiniteCodingManningCorrespondence
public import LeanShared.Dynamics.FiniteCodingMatchingImages

/-! Outside the single higher-matching image, an actual periodic base
point has exactly one original symbolic lift, and that lift returns at
the original period.  This is proved using the invariant WHOLE return
fiber, rather than assuming boundary uniqueness of arbitrary labels.
-/

public noncomputable section
namespace LeanShared.FiniteCodingManning
open Set Function BilateralShadowingCoding MarkovFinitePathRealization
variable {A X : Type*} [MetricSpace X] [TopologicalSpace A] [Fintype A] [DecidableEq A]

theorem periodicFiber_subsingleton_off_higher (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (properties : FiniteCodingGeometry T rectangles code)
    (x : X) (period : ℕ) (positive : 0 < period) (fixed : (T : X → X)^[period] x = x)
    (outside : x ∉ higherMatchingImage T rectangles code) : Subsingleton (code ⁻¹' {x}) := by
  classical
  let : Fintype (code ⁻¹' {x}) := (properties.finiteFibers x).fintype
  refine ⟨fun a b => ?_⟩
  by_contra different
  have atLeastTwo : 1 < Fintype.card (code ⁻¹' {x}) := Fintype.one_lt_card_iff.mpr ⟨a, b, different⟩
  have atMostSymbols : Fintype.card (code ⁻¹' {x}) ≤ Fintype.card A :=
    Fintype.card_le_of_injective (fun p : code ⁻¹' {x} => p.val.val 0)
      (properties.periodicSymbols x period positive fixed 0)
  let k := Fintype.card (code ⁻¹' {x}) - 1
  have positiveK : 0 < k := by dsimp [k]; omega
  have card : (Finset.univ : Finset (code ⁻¹' {x})).card = k + 1 := by
    simp only [Finset.card_univ]
    dsimp [k]
    omega
  obtain ⟨P, returns⟩ := properties.returnPermutation x period fixed
  obtain ⟨walk, inside, _subset, _periodic, _sign⟩ :=
    periodic_fiber_subset_matching_exact T rectangles code properties x period positive fixed P returns
      Finset.univ (fun _ => by simp only [Finset.mem_univ]) k card
  apply outside
  change x ∈ ⋃ j : Fin (Fintype.card A), Set.range (matchingCode T rectangles code (j.val + 1))
  refine mem_iUnion.mpr ⟨⟨k - 1, by dsimp [k]; omega⟩, ?_⟩
  have order : k - 1 + 1 = k := by omega
  change x ∈ Set.range (matchingCode T rectangles code (k - 1 + 1))
  rw [order]
  exact ⟨walk, inside⟩

@[expose] def PeriodicCodeFiber (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (x : X) (period : ℕ) :=
  {a : code ⁻¹' {x} // (shift (Transition T rectangles) : _ → _)^[period] a.val = a.val}

omit [DecidableEq A] in
theorem periodicCodeFiber_card_bound (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (properties : FiniteCodingGeometry T rectangles code)
    (x : X) (period : ℕ) :
    Nat.card (PeriodicCodeFiber T rectangles code x period) ≤ (Fintype.card A) ^ 2 := by
  let : Finite (code ⁻¹' {x}) := Set.finite_coe_iff.mpr (properties.finiteFibers x)
  have count := Nat.card_le_card_of_injective
    (fun a : PeriodicCodeFiber T rectangles code x period => a.val) Subtype.val_injective
  exact count.trans (by simpa only [Nat.card_coe_set_eq] using (properties.fibers x).2)

theorem periodicCodeFiber_card_one_off_higher (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (properties : FiniteCodingGeometry T rectangles code)
    (x : X) (period : ℕ) (positive : 0 < period) (fixed : (T : X → X)^[period] x = x)
    (outside : x ∉ higherMatchingImage T rectangles code) :
    Nat.card (PeriodicCodeFiber T rectangles code x period) = 1 := by
  have singleton := periodicFiber_subsingleton_off_higher T rectangles code properties x period positive fixed outside
  obtain ⟨a, coded⟩ := properties.onto x
  let lift : code ⁻¹' {x} := ⟨a, coded⟩
  obtain ⟨P, returns⟩ := properties.returnPermutation x period fixed
  have identity : P lift = lift := singleton.elim _ _
  have actualReturn : (shift (Transition T rectangles) : _ → _)^[period] a = a := by
    have returned := returns lift
    rw [identity] at returned
    exact returned.symm
  let point : PeriodicCodeFiber T rectangles code x period := ⟨lift, actualReturn⟩
  let : Unique (PeriodicCodeFiber T rectangles code x period) :=
    { default := point, uniq := fun b => Subtype.ext (singleton.elim b.val point.val) }
  exact Nat.card_unique

end LeanShared.FiniteCodingManning
