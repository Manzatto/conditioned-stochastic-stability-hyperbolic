module

public import LeanShared.Dynamics.FiniteCodingPeriodicAmbiguity
public import LeanShared.Dynamics.ActualBilateralWeightedZeta

/-! Exact regrouping of literal main symbolic periodic weights over the
actual base fixed points.  Their difference is bounded by the periodic
weights on the proper higher matching image, with a period-independent
constant.  No pressure or finite-extension entropy identity is assumed.
-/

public noncomputable section
namespace LeanShared.FiniteCodingManning
open Set Function BilateralShadowingCoding MarkovFinitePathRealization ThermodynamicDefinitions
variable {A X : Type*} [MetricSpace X] [TopologicalSpace A] [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
theorem periodicCodeFiber_finite (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (properties : FiniteCodingGeometry T rectangles code)
    (x : X) (n : ℕ) : Finite (PeriodicCodeFiber T rectangles code x n) := by
  let : Finite (code ⁻¹' {x}) := Set.finite_coe_iff.mpr (properties.finiteFibers x)
  exact Finite.of_injective (fun a : PeriodicCodeFiber T rectangles code x n => a.val) Subtype.val_injective

@[expose] def periodicCodingFiberEquiv (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (properties : FiniteCodingGeometry T rectangles code)
    (n : ℕ) (P : Finset X) (complete : ∀ x, x ∈ P ↔ (T : X → X)^[n] x = x) :
    PeriodicBilateral (R := Transition T rectangles) n ≃
      Σ x : P, PeriodicCodeFiber T rectangles code x.val n where
  toFun p :=
    ⟨⟨code p.val, (complete _).mpr (by
      rw [← code_shift_iterate T rectangles code properties.intertwines, p.property])⟩,
      ⟨⟨p.val, rfl⟩, p.property⟩⟩
  invFun p := ⟨p.2.val.val, p.2.property⟩
  left_inv p := rfl
  right_inv p := by
    rcases p with ⟨⟨x, hx⟩, ⟨⟨a, coded⟩, periodic⟩⟩
    change code a = x at coded
    subst x
    rfl

omit [DecidableEq A] in
theorem bilateralPeriodicWeightSum_fibers (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (properties : FiniteCodingGeometry T rectangles code)
    (φ : X → ℝ) (n : ℕ) [NeZero n] (P : Finset X)
    (complete : ∀ x, x ∈ P ↔ (T : X → X)^[n] x = x) :
    bilateralPeriodicWeightSum (φ ∘ code) n =
      ∑ x ∈ P, (Nat.card (PeriodicCodeFiber T rectangles code x n) : ℝ) * Real.exp (orbitSum T φ n x) := by
  classical
  let (x : P) : Finite (PeriodicCodeFiber T rectangles code x.val n) :=
    periodicCodeFiber_finite T rectangles code properties x.val n
  let (x : P) : Fintype (PeriodicCodeFiber T rectangles code x.val n) := Fintype.ofFinite _
  have sums := Equiv.sum_comp (periodicCodingFiberEquiv T rectangles code properties n P complete)
    (fun p : Σ x : P, PeriodicCodeFiber T rectangles code x.val n => Real.exp (orbitSum T φ n p.1.val))
  calc
    _ = ∑ p : PeriodicBilateral (R := Transition T rectangles) n, Real.exp (orbitSum T φ n (code p.val)) := by
      exact Finset.sum_congr rfl (fun p _ => congrArg Real.exp
        (orbitSum_of_semiconjugacy code (shift (Transition T rectangles)) T properties.intertwines φ n p.val))
    _ = ∑ p : Σ x : P, PeriodicCodeFiber T rectangles code x.val n,
        Real.exp (orbitSum T φ n p.1.val) := sums
    _ = ∑ x : P, (Nat.card (PeriodicCodeFiber T rectangles code x.val n) : ℝ) * Real.exp (orbitSum T φ n x.val) := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro x _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    _ = _ := Finset.sum_coe_sort P (fun x : X =>
      (Nat.card (PeriodicCodeFiber T rectangles code x n) : ℝ) * Real.exp (orbitSum T φ n x))

@[expose] def periodicHigherSubset (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (P : Finset X) : Finset X := by
  classical
  exact P.filter (fun x => x ∈ higherMatchingImage T rectangles code)

theorem periodic_weight_comparison (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (properties : FiniteCodingGeometry T rectangles code)
    (φ : X → ℝ) (n : ℕ) [NeZero n] (P : Finset X)
    (complete : ∀ x, x ∈ P ↔ (T : X → X)^[n] x = x) :
    |bilateralPeriodicWeightSum (φ ∘ code) n - ∑ x ∈ P, Real.exp (orbitSum T φ n x)| ≤
      ((Fintype.card A : ℝ) ^ 2 + 1) *
        ∑ x ∈ periodicHigherSubset T rectangles code P, Real.exp (orbitSum T φ n x) := by
  classical
  rw [bilateralPeriodicWeightSum_fibers T rectangles code properties φ n P complete, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [periodicHigherSubset, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro x hx
  let q : ℝ := Nat.card (PeriodicCodeFiber T rectangles code x n)
  have nonnegativeQ : 0 ≤ q := by dsimp [q]; positivity
  have countBound : q ≤ (Fintype.card A : ℝ) ^ 2 := by
    dsimp only [q]
    exact_mod_cast periodicCodeFiber_card_bound T rectangles code properties x n
  by_cases inside : x ∈ higherMatchingImage T rectangles code
  · rw [ite_eq_left inside]
    have difference : |q - 1| ≤ (Fintype.card A : ℝ) ^ 2 + 1 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      _ = |q - 1| * Real.exp (orbitSum T φ n x) := by
        change |q * Real.exp (orbitSum T φ n x) - Real.exp (orbitSum T φ n x)| = _
        have factor : q * Real.exp (orbitSum T φ n x) - Real.exp (orbitSum T φ n x) =
            (q - 1) * Real.exp (orbitSum T φ n x) := by ring
        rw [factor, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ _ := mul_le_mul_of_nonneg_right difference (Real.exp_pos _).le
  · rw [ite_eq_right inside]
    have one := periodicCodeFiber_card_one_off_higher T rectangles code properties x n
      (Nat.pos_of_ne_zero (NeZero.ne n)) ((complete x).mp hx) inside
    simp only [one, Nat.cast_one, one_mul, sub_self, abs_zero, le_refl]

end LeanShared.FiniteCodingManning
