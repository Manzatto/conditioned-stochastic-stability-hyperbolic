module
public import LeanShared.Analysis.ActualWordMicrolocalBound
public import LeanShared.Analysis.CylinderPrincipalCoefficient

/-! The chronological list word of finite-regular composition is the
prefix orbit of the corresponding control word, and its real accumulated
weight is the product of the weight along that prefix orbit. -/
public noncomputable section
namespace LeanShared.ActualWordPrefixOrbit
open CylinderPrincipalCoefficient
variable {Ω G X : Type*}

theorem prefixOrbit_succ_tail (Φ : G → X → X) {N : ℕ} (control : Fin (N + 1) → G) :
    ∀ (k : ℕ) (x : X), prefixOrbit Φ control (k + 1) x =
      prefixOrbit Φ (Fin.tail control) k (Φ (control 0) x) := by
  intro k
  induction k with
  | zero =>
    intro x
    simp only [prefixOrbit, Nat.zero_lt_succ, dite_true]
    rfl
  | succ k ih =>
    intro x
    by_cases h : k < N
    · have h' : k + 1 < N + 1 := Nat.succ_lt_succ h
      conv_lhs => rw [prefixOrbit, dite_eq_left_of_eq_true (eq_true h'), ih]
      conv_rhs => rw [prefixOrbit, dite_eq_left_of_eq_true (eq_true h)]
      rfl
    · have h' : ¬ k + 1 < N + 1 := fun hk => h (Nat.lt_of_succ_lt_succ hk)
      conv_lhs => rw [prefixOrbit, dite_eq_right_of_eq_false (eq_false h'), ih]
      conv_rhs => rw [prefixOrbit, dite_eq_right_of_eq_false (eq_false h)]

theorem orbit_ofFn (F : Ω → X → X) (Φ : G → X → X) :
    ∀ {N : ℕ} (word : Fin N → Ω) (control : Fin N → G),
    (∀ k, F (word k) = Φ (control k)) → ∀ x,
    ActualFiniteRegularWord.orbit F (List.ofFn word) x = prefixOrbit Φ control N x := by
  intro N
  induction N with
  | zero => intro _ _ _ x; rfl
  | succ N ih =>
    intro word control same x
    rw [List.ofFn_succ, prefixOrbit_succ_tail]
    change ActualFiniteRegularWord.orbit F (List.ofFn fun i => word i.succ) (F (word 0) x) = _
    rw [same 0]
    exact ih (fun i => word i.succ) (Fin.tail control) (fun i => same i.succ) _

theorem realWeight_ofFn (F : Ω → X → X) (Φ : G → X → X) (g : X → ℝ) :
    ∀ {N : ℕ} (word : Fin N → Ω) (control : Fin N → G),
    (∀ k, F (word k) = Φ (control k)) → ∀ x,
    ActualWordMicrolocalBound.realWeight F g (List.ofFn word) x =
      ∏ k ∈ Finset.range N, g (prefixOrbit Φ control k x) := by
  intro N
  induction N with
  | zero => intro _ _ _ x; rfl
  | succ N ih =>
    intro word control same x
    rw [List.ofFn_succ, Finset.prod_range_succ']
    change g x * ActualWordMicrolocalBound.realWeight F g (List.ofFn fun i => word i.succ)
      (F (word 0) x) = _
    rw [same 0, ih (fun i => word i.succ) (Fin.tail control) (fun i => same i.succ), mul_comm]
    congr 1
    · apply Finset.prod_congr rfl
      intro k _
      rw [prefixOrbit_succ_tail]

end LeanShared.ActualWordPrefixOrbit
