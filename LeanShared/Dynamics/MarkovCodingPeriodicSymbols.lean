module

public import LeanShared.Dynamics.MarkovCodingPeriodicFibers
public import LeanShared.Dynamics.FiniteSymbolicWindowPasting

/-! Distinct lifts over a periodic point have distinct labels at every
time, including boundary labels.  Translation preserves the proved
pointwise affiliation relation, so time-zero periodic separation applies.
-/

public noncomputable section
namespace LeanShared.MarkovFinitePathRealization
open Set Function BilateralShadowingCoding
variable {X I : Type*} [MetricSpace X] [TopologicalSpace I]

omit [TopologicalSpace I] in
theorem periodic_lifts_eq_of_symbol_eq_at (T : X ≃ₜ X) (rectangles : I → Set X)
    (code : Path (Transition T rectangles) → X)
    (geometry : HasSymbolicFiberGeometry T rectangles code)
    (a b : Path (Transition T rectangles)) (samePoint : code a = code b)
    (p : ℕ) (positive : 0 < p)
    (periodicA : Function.Periodic a.val (p : ℤ))
    (periodicB : Function.Periodic b.val (p : ℤ))
    (k : ℤ) (sameSymbol : a.val k = b.val k) : a = b := by
  have translatedSame : code (translatePath a k) = code (translatePath b k) := by
    apply (geometry.1 _ _).mpr
    exact fun j => (geometry.1 a b).mp samePoint (j + k)
  have periodicTranslatedA : Function.Periodic (translatePath a k).val (p : ℤ) := by
    intro j
    change a.val (j + p + k) = a.val (j + k)
    simpa only [add_right_comm] using periodicA (j + k)
  have periodicTranslatedB : Function.Periodic (translatePath b k).val (p : ℤ) := by
    intro j
    change b.val (j + p + k) = b.val (j + k)
    simpa only [add_right_comm] using periodicB (j + k)
  have equal := periodic_lifts_eq_of_symbol_eq T rectangles code geometry
    (translatePath a k) (translatePath b k) translatedSame p positive
    periodicTranslatedA periodicTranslatedB (by simpa only [translatePath, zero_add] using sameSymbol)
  apply Subtype.ext
  funext j
  have coordinate := congrArg (fun d : Path (Transition T rectangles) => d.val (j - k)) equal
  simpa only [translatePath, sub_add_cancel] using coordinate

theorem periodic_fiber_coordinate_injective (T : X ≃ₜ X) (rectangles : I → Set X)
    (code : Path (Transition T rectangles) → X)
    (intertwines : ∀ a, code (shift (Transition T rectangles) a) = T (code a))
    (finiteFibers : ∀ x, (code ⁻¹' {x}).Finite)
    (geometry : HasSymbolicFiberGeometry T rectangles code)
    (x : X) (n : ℕ) (positive : 0 < n) (fixed : (T : X → X)^[n] x = x) (k : ℤ) :
    Injective (fun a : code ⁻¹' {x} => a.val.val k) := by
  intro a b sameSymbol
  have fixedA : (T : X → X)^[n] (code a.val) = code a.val := by
    rw [show code a.val = x from a.property]
    exact fixed
  have fixedB : (T : X → X)^[n] (code b.val) = code b.val := by
    rw [show code b.val = x from b.property]
    exact fixed
  obtain ⟨p, positiveP, periodA⟩ := periodic_base_lift_periodic T rectangles code intertwines finiteFibers a.val n positive fixedA
  obtain ⟨q, positiveQ, periodB⟩ := periodic_base_lift_periodic T rectangles code intertwines finiteFibers b.val n positive fixedB
  apply Subtype.ext
  apply periodic_lifts_eq_of_symbol_eq_at T rectangles code geometry a.val b.val
    ((show code a.val = x from a.property).trans (show code b.val = x from b.property).symm)
    (p * q) (Nat.mul_pos positiveP positiveQ)
  · simpa only [Nat.cast_mul, mul_comm] using periodA.nat_mul q
  · simpa only [Nat.cast_mul] using periodB.nat_mul p
  · exact sameSymbol

end LeanShared.MarkovFinitePathRealization
