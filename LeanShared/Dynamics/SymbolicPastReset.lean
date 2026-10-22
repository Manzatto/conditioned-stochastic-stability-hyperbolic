module

public import LeanShared.Dynamics.FiniteSymbolicWindowPasting
public import LeanShared.Dynamics.SymbolicExponentialVariation
public import LeanShared.Dynamics.MarkovCodingPeriodicFibers

/-! A literal canonical past reset on an arbitrary finite-graph path
space.  It keeps all nonnegative coordinates and attaches a chosen
admissible past with the same time-zero symbol.  No mixing, full shift,
or preselected extension field is assumed.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization
variable {A : Type*} {R : A → A → Prop}

@[expose] def FutureAgreement (a b : Path R) : Prop :=
  ∀ n : ℤ, 0 ≤ n → a.val n = b.val n

@[expose] def referencePath (i : A) (witness : ∃ a : Path R, a.val 0 = i) : Path R :=
  Classical.choose witness

theorem referencePath_zero (i : A) (witness : ∃ a : Path R, a.val 0 = i) :
    (referencePath i witness).val 0 = i := Classical.choose_spec witness

theorem referencePath_congr (i j : A) (hi : ∃ a : Path R, a.val 0 = i)
    (hj : ∃ a : Path R, a.val 0 = j) (equal : i = j) : referencePath i hi = referencePath j hj := by
  subst j
  rfl

@[expose] def pastReset (a : Path R) : Path R :=
  pasteWindow (referencePath (a.val 0) ⟨a, rfl⟩) a a 0 0 (by omega)
    (referencePath_zero _ _) rfl

theorem pastReset_future (a : Path R) (n : ℤ) (nonnegative : 0 ≤ n) :
    (pastReset a).val n = a.val n := by
  simp only [pastReset, pasteWindow, ite_eq_right (by omega : ¬ n < 0), ite_self]

theorem pastReset_past (a : Path R) (n : ℤ) (negative : n < 0) :
    (pastReset a).val n = (referencePath (a.val 0) ⟨a, rfl⟩).val n := by
  simp only [pastReset, pasteWindow, ite_eq_left negative]

theorem pastReset_eq_of_future (a b : Path R) (same : FutureAgreement a b) : pastReset a = pastReset b := by
  have zero := same 0 (by omega)
  have references := referencePath_congr (a.val 0) (b.val 0) ⟨a, rfl⟩ ⟨b, rfl⟩ zero
  apply Subtype.ext
  funext n
  by_cases negative : n < 0
  · rw [pastReset_past a n negative, pastReset_past b n negative, references]
  · rw [pastReset_future a n (by omega), pastReset_future b n (by omega)]
    exact same n (by omega)

theorem pastReset_idempotent (a : Path R) : pastReset (pastReset a) = pastReset a :=
  pastReset_eq_of_future _ _ (fun n nonnegative => pastReset_future a n nonnegative)

theorem pastReset_windowAgreement (a b : Path R) (radius : ℕ)
    (same : WindowAgreement a b radius) : WindowAgreement (pastReset a) (pastReset b) radius := by
  have zero := same 0 (by omega) (by omega)
  have references := referencePath_congr (a.val 0) (b.val 0) ⟨a, rfl⟩ ⟨b, rfl⟩ zero
  intro n lower upper
  by_cases negative : n < 0
  · rw [pastReset_past a n negative, pastReset_past b n negative, references]
  · rw [pastReset_future a n (by omega), pastReset_future b n (by omega)]
    exact same n lower upper

variable [TopologicalSpace A]

theorem shift_pastReset_window (a : Path R) (n : ℕ) :
    WindowAgreement ((shift R : _ → _)^[n] a) ((shift R : _ → _)^[n] (pastReset a)) n := by
  intro k lower _upper
  rw [shift_iterate_val, shift_iterate_val, pastReset_future _ _ (by omega)]

theorem pastReset_continuous [DiscreteTopology A] : Continuous (pastReset : Path R → Path R) := by
  let admitted := {i : A // ∃ a : Path R, a.val 0 = i}
  let symbol : Path R → admitted := fun a => ⟨a.val 0, ⟨a, rfl⟩⟩
  have symbolContinuous : Continuous symbol :=
    ((continuous_apply 0).comp continuous_subtype_val).subtype_mk _
  let reference : admitted → Path R := fun i => referencePath i.val i.property
  have referenceContinuous : Continuous reference := continuous_of_discreteTopology
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  by_cases negative : n < 0
  · have coordinate := (continuous_apply n).comp (continuous_subtype_val.comp (referenceContinuous.comp symbolContinuous))
    simp only [ite_eq_left negative]
    change Continuous (fun a : Path R => (referencePath (a.val 0) ⟨a, rfl⟩).val n) at coordinate
    exact coordinate
  · have coordinate : Continuous (fun a : Path R => a.val n) :=
      (continuous_apply n).comp continuous_subtype_val
    simpa only [ite_eq_right negative, ite_self] using coordinate

end LeanShared.BilateralShadowingCoding
