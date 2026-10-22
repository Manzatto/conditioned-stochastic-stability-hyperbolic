module

public import LeanShared.Dynamics.MarkovCodingPeriodicSeparation
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! Finite literal coding fibers over periodic points consist of periodic
symbolic paths.  The return shift is an injective self-map of the finite
fiber, so every lift returns.  No periodic lifting assumption is used.
-/

public noncomputable section
namespace LeanShared.MarkovFinitePathRealization
open Set Function BilateralShadowingCoding
variable {X I : Type*} [MetricSpace X] [TopologicalSpace I]

theorem shift_iterate_val {R : I → I → Prop} (a : Path R) (n : ℕ) (k : ℤ) :
    (((shift R : Path R → Path R)^[n]) a).val k = a.val (k + n) := by
  induction n generalizing k with
  | zero => simp only [iterate_zero_apply, Nat.cast_zero, add_zero]
  | succ n induction =>
    rw [iterate_succ_apply', shift_apply, induction]
    apply congrArg a.val
    omega

theorem code_shift_iterate (T : X ≃ₜ X) (rectangles : I → Set X)
    (code : Path (Transition T rectangles) → X)
    (intertwines : ∀ a, code (shift (Transition T rectangles) a) = T (code a))
    (n : ℕ) (a : Path (Transition T rectangles)) :
    code ((shift (Transition T rectangles) : _ → _)^[n] a) = (T : X → X)^[n] (code a) := by
  induction n with
  | zero => rfl
  | succ n induction => rw [iterate_succ_apply', intertwines, induction, iterate_succ_apply']

theorem periodic_base_lift_periodic (T : X ≃ₜ X) (rectangles : I → Set X)
    (code : Path (Transition T rectangles) → X)
    (intertwines : ∀ a, code (shift (Transition T rectangles) a) = T (code a))
    (finiteFibers : ∀ x, (code ⁻¹' {x}).Finite)
    (a : Path (Transition T rectangles)) (n : ℕ) (positive : 0 < n)
    (fixed : (T : X → X)^[n] (code a) = code a) :
    ∃ p : ℕ, 0 < p ∧ Function.Periodic a.val (p : ℤ) := by
  let fiber := code ⁻¹' {code a}
  let : Fintype fiber := (finiteFibers (code a)).fintype
  let σ : Path (Transition T rectangles) → Path (Transition T rectangles) :=
    (shift (Transition T rectangles) : _ → _)^[n]
  have stays (b : fiber) : σ b.val ∈ fiber := by
    change code (σ b.val) = code a
    rw [code_shift_iterate T rectangles code intertwines n b.val]
    exact (congrArg ((T : X → X)^[n]) b.property).trans fixed
  let f : fiber → fiber := fun b => ⟨σ b.val, stays b⟩
  have injective : Injective f := by
    intro b c equal
    apply Subtype.ext
    exact ((shift (Transition T rectangles)).injective.iterate n)
      (congrArg (fun b : fiber => b.val) equal)
  obtain ⟨m, positiveM, returns⟩ := Function.mem_periodicPts.mp
    (injective.mem_periodicPts (⟨a, rfl⟩ : fiber))
  have lifts (m : ℕ) (b : fiber) : (f^[m] b).val = σ^[m] b.val := by
    induction m with
    | zero => rfl
    | succ m induction =>
      rw [iterate_succ_apply', iterate_succ_apply']
      exact congrArg σ induction
  have returnPath : ((shift (Transition T rectangles) : _ → _)^[n * m]) a = a := by
    rw [iterate_mul]
    exact (lifts m ⟨a, rfl⟩).symm.trans (congrArg (fun b : fiber => b.val) returns)
  refine ⟨n * m, Nat.mul_pos positive positiveM, fun k => ?_⟩
  have coordinate := congrArg (fun b : Path (Transition T rectangles) => b.val k) returnPath
  simpa only [shift_iterate_val] using coordinate

theorem periodic_fiber_symbol_injective (T : X ≃ₜ X) (rectangles : I → Set X)
    (code : Path (Transition T rectangles) → X)
    (intertwines : ∀ a, code (shift (Transition T rectangles) a) = T (code a))
    (finiteFibers : ∀ x, (code ⁻¹' {x}).Finite)
    (geometry : HasSymbolicFiberGeometry T rectangles code)
    (x : X) (n : ℕ) (positive : 0 < n) (fixed : (T : X → X)^[n] x = x) :
    Injective (fun a : code ⁻¹' {x} => a.val.val 0) := by
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
  apply periodic_lifts_eq_of_symbol_eq T rectangles code geometry a.val b.val
    ((show code a.val = x from a.property).trans (show code b.val = x from b.property).symm)
    (p * q) (Nat.mul_pos positiveP positiveQ)
  · simpa only [Nat.cast_mul, mul_comm] using periodA.nat_mul q
  · simpa only [Nat.cast_mul] using periodB.nat_mul p
  · exact sameSymbol

theorem exists_fiber_return_equiv (T : X ≃ₜ X) (rectangles : I → Set X)
    (code : Path (Transition T rectangles) → X)
    (intertwines : ∀ a, code (shift (Transition T rectangles) a) = T (code a))
    (finiteFibers : ∀ x, (code ⁻¹' {x}).Finite)
    (x : X) (n : ℕ) (fixed : (T : X → X)^[n] x = x) :
    ∃ P : (code ⁻¹' {x}) ≃ (code ⁻¹' {x}), ∀ a,
      (P a).val = (shift (Transition T rectangles) : _ → _)^[n] a.val := by
  let fiber := code ⁻¹' {x}
  let : Fintype fiber := (finiteFibers x).fintype
  let σ : Path (Transition T rectangles) → Path (Transition T rectangles) :=
    (shift (Transition T rectangles) : _ → _)^[n]
  have stays (a : fiber) : σ a.val ∈ fiber := by
    change code (σ a.val) = x
    rw [code_shift_iterate T rectangles code intertwines n a.val]
    exact (congrArg ((T : X → X)^[n]) a.property).trans fixed
  let f : fiber → fiber := fun a => ⟨σ a.val, stays a⟩
  have injective : Injective f := by
    intro a b equal
    apply Subtype.ext
    exact ((shift (Transition T rectangles)).injective.iterate n)
      (congrArg (fun a : fiber => a.val) equal)
  exact ⟨Equiv.ofBijective f ⟨injective, (Finite.injective_iff_surjective).mp injective⟩, fun _ => rfl⟩

end LeanShared.MarkovFinitePathRealization
