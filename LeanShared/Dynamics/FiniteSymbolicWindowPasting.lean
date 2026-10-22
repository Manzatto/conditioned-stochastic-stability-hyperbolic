module

public import LeanShared.Dynamics.MarkovItineraryWindows

/-! Paste two genuine symbolic tails around a prescribed finite graph
word.  Any orbit staying in that word's cylinder images on the finite
window has a code with precisely those symbols, by shadowing uniqueness.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function BilateralHomeomorphismOrbit MarkovFinitePathRealization
variable {A X : Type*} [TopologicalSpace A] [MetricSpace X] {R : A → A → Prop}

@[expose] def translatePath (a : Path R) (time : ℤ) : Path R :=
  ⟨fun n => a.val (n + time), fun n => by
    simpa only [add_right_comm] using a.property (n + time)⟩

@[expose] def pasteWindow (past middle future : Path R) (left right : ℤ) (ordered : left ≤ right)
    (leftSymbol : past.val left = middle.val left) (rightSymbol : future.val right = middle.val right) : Path R :=
  ⟨fun n => if n < left then past.val n else if n ≤ right then middle.val n else future.val n, by
    intro n
    by_cases before : n < left
    · by_cases beforeNext : n + 1 < left
      · simpa only [ite_eq_left before, ite_eq_left beforeNext] using past.property n
      · have boundary : n + 1 = left := by omega
        have nextInside : n + 1 ≤ right := by omega
        simp only [ite_eq_left before, ite_eq_right beforeNext, ite_eq_left nextInside]
        rw [boundary, ← leftSymbol]
        simpa only [boundary] using past.property n
    · have beforeNext : ¬n + 1 < left := by omega
      by_cases within : n ≤ right
      · by_cases withinNext : n + 1 ≤ right
        · simpa only [ite_eq_right before, ite_eq_right beforeNext, ite_eq_left within,
            ite_eq_left withinNext] using middle.property n
        · have boundary : n = right := by omega
          simp only [ite_eq_right before, ite_eq_right beforeNext, ite_eq_left within,
            ite_eq_right withinNext]
          rw [boundary, ← rightSymbol]
          exact future.property right
      · have withinNext : ¬n + 1 ≤ right := by omega
        simpa only [ite_eq_right before, ite_eq_right beforeNext, ite_eq_right within,
          ite_eq_right withinNext] using future.property n⟩

omit [TopologicalSpace A] [MetricSpace X] in
theorem pasteWindow_middle (past middle future : Path R) (left right : ℤ) (ordered : left ≤ right)
    (leftSymbol : past.val left = middle.val left) (rightSymbol : future.val right = middle.val right)
    (n : ℤ) (lower : left ≤ n) (upper : n ≤ right) :
    (pasteWindow past middle future left right ordered leftSymbol rightSymbol).val n = middle.val n := by
  simp only [pasteWindow, ite_eq_right (by omega : ¬n < left), ite_eq_left upper]

omit [TopologicalSpace A] in
/-- A literal finite cylinder itinerary lifts to the same finite graph
word, by adjoining actual symbolic tails at its endpoints. -/
theorem finite_window_lift (T : X ≃ₜ X) (center : A → X) (code : Path R → X) (c ε : ℝ)
    (expansive : ∀ x y : X, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)
    (small : 2 * ε ≤ c)
    (near : ∀ a n, dist (orbit T (code a) n) (center (a.val (-n))) ≤ ε)
    (middle : Path R) (left right : ℤ) (ordered : left ≤ right) (x : X)
    (inside : ∀ k : ℤ, left ≤ k → k ≤ right → (T ^ k) x ∈ rectangle code (middle.val k)) :
    ∃ a : Path R, code a = x ∧ ∀ k : ℤ, left ≤ k → k ≤ right → a.val k = middle.val k := by
  obtain ⟨pastCode, pastSymbol, codedPast⟩ := inside left le_rfl ordered
  obtain ⟨futureCode, futureSymbol, codedFuture⟩ := inside right ordered le_rfl
  change pastCode.val 0 = middle.val left at pastSymbol
  change futureCode.val 0 = middle.val right at futureSymbol
  let past := translatePath pastCode (-left)
  let future := translatePath futureCode (-right)
  have leftSymbol : past.val left = middle.val left := by
    change pastCode.val (left + -left) = middle.val left
    simpa only [add_neg_cancel] using pastSymbol
  have rightSymbol : future.val right = middle.val right := by
    change futureCode.val (right + -right) = middle.val right
    simpa only [add_neg_cancel] using futureSymbol
  let a := pasteWindow past middle future left right ordered leftSymbol rightSymbol
  have shadows (n : ℤ) : dist (orbit T x n) (center (a.val (-n))) ≤ ε := by
    by_cases before : -n < left
    · have estimate := near pastCode (n + left)
      have time : orbit T (code pastCode) (n + left) = orbit T x n := by
        rw [codedPast]
        change (T ^ (-(n + left))) ((T ^ left) x) = (T ^ (-n)) x
        rw [pow_apply_time_shift]
        exact congrArg (fun k : ℤ => (T ^ k) x) (by omega : -(n + left) + left = -n)
      have symbol : a.val (-n) = pastCode.val (-(n + left)) := by
        change (if -n < left then past.val (-n) else if -n ≤ right then middle.val (-n) else future.val (-n)) = _
        rw [ite_eq_left before]
        change pastCode.val (-n + -left) = pastCode.val (-(n + left))
        rw [neg_add]
      rw [time] at estimate
      simpa only [symbol] using estimate
    · by_cases within : -n ≤ right
      · have membership := inside (-n) (by omega) within
        obtain ⟨b, symbol, coded⟩ := membership
        have estimate := near b 0
        simp only [zero, neg_zero] at estimate
        rw [symbol, coded] at estimate
        have matchSymbol : a.val (-n) = middle.val (-n) :=
          pasteWindow_middle past middle future left right ordered leftSymbol rightSymbol (-n) (by omega) within
        change dist ((T ^ (-n)) x) (center (a.val (-n))) ≤ ε
        rw [matchSymbol]
        exact estimate
      · have estimate := near futureCode (n + right)
        have time : orbit T (code futureCode) (n + right) = orbit T x n := by
          rw [codedFuture]
          change (T ^ (-(n + right))) ((T ^ right) x) = (T ^ (-n)) x
          rw [pow_apply_time_shift]
          exact congrArg (fun k : ℤ => (T ^ k) x) (by omega : -(n + right) + right = -n)
        have symbol : a.val (-n) = futureCode.val (-(n + right)) := by
          change (if -n < left then past.val (-n) else if -n ≤ right then middle.val (-n) else future.val (-n)) = _
          rw [ite_eq_right before, ite_eq_right within]
          change futureCode.val (-n + -right) = futureCode.val (-(n + right))
          rw [neg_add]
        rw [time] at estimate
        simpa only [symbol] using estimate
  exact ⟨a, shadow_unique T c ε expansive small _ (code a) x (near a) shadows,
    fun k lower upper => pasteWindow_middle past middle future left right ordered leftSymbol rightSymbol k lower upper⟩

end LeanShared.BilateralShadowingCoding
