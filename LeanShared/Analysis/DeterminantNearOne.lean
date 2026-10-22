module
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! Determinants near the identity. A Leibniz expansion bounds
`|det(1 - Z) - 1|` linearly in the entries of `Z`; in a finite-dimensional normed
space this gives `|det(1 - Z) - 1| ≤ L ‖Z‖` for small `‖Z‖`. Also Sylvester's
identity `det(1 - f g) = det(1 - g f)` for endomorphisms, and the elementary product
bounds `∏ (1 - x) ≥ exp(-2 ∑ x)`, `∏ (1 + x) ≤ exp(∑ x)` for `0 ≤ x ≤ 1/2`. -/
public noncomputable section
open Finset
namespace LeanShared.DeterminantNearOne

theorem prod_near_one {ι : Type*} (s : Finset ι) (x : ι → ℝ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hx : ∀ i ∈ s, |x i - 1| ≤ ε) : |∏ i ∈ s, x i - 1| ≤ s.card * 2 ^ s.card * ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, card_insert_of_notMem ha]
    have hxa := hx a (mem_insert_self a s)
    have ih' := ih (fun i hi => hx i (mem_insert_of_mem hi))
    have xa : |x a| ≤ 2 := by
      have := abs_sub_abs_le_abs_sub (x a) 1
      rw [abs_one] at this
      linarith
    have key : x a * ∏ i ∈ s, x i - 1 = x a * (∏ i ∈ s, x i - 1) + (x a - 1) := by ring
    rw [key]
    have pow1 : (1 : ℝ) ≤ 2 ^ s.card := one_le_pow₀ (by norm_num)
    calc |x a * (∏ i ∈ s, x i - 1) + (x a - 1)| ≤ |x a| * |∏ i ∈ s, x i - 1| + |x a - 1| := by
          rw [← abs_mul]
          exact abs_add_le _ _
      _ ≤ 2 * (s.card * 2 ^ s.card * ε) + ε :=
          add_le_add (mul_le_mul xa ih' (abs_nonneg _) (by norm_num)) hxa
      _ ≤ ((s.card + 1 : ℕ) : ℝ) * 2 ^ (s.card + 1) * ε := by
          push_cast
          rw [pow_succ]
          nlinarith [mul_nonneg h0 (sub_nonneg.mpr pow1)]

theorem matrix_det_one_sub {d : ℕ} (Z : Matrix (Fin d) (Fin d) ℝ) (ε : ℝ) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) (hZ : ∀ i j, |Z i j| ≤ ε) :
    |(1 - Z).det - 1| ≤ (d * 2 ^ d + d.factorial * 2 ^ d) * ε := by
  classical
  rw [Matrix.det_apply, ← add_sum_erase _ _ (mem_univ (1 : Equiv.Perm (Fin d)))]
  have entry (i j : Fin d) : (1 - Z) i j = (if i = j then 1 else 0) - Z i j := by
    simp only [Matrix.sub_apply, Matrix.one_apply]
  have identity : |Equiv.Perm.sign (1 : Equiv.Perm (Fin d)) •
      ∏ i, (1 - Z) ((1 : Equiv.Perm (Fin d)) i) i - 1| ≤ d * 2 ^ d * ε := by
    simp only [Equiv.Perm.sign_one, one_smul, Equiv.Perm.one_apply]
    have := prod_near_one univ (fun i => (1 - Z) i i) ε h0 h1 (fun i _ => by
      rw [entry]
      simp only [↓reduceIte, sub_sub_cancel_left, abs_neg]
      exact hZ i i)
    simpa only [card_univ, Fintype.card_fin] using this
  have bounded (σ : Equiv.Perm (Fin d)) (i : Fin d) : |(1 - Z) (σ i) i| ≤ 2 := by
    rw [entry]
    calc |(if σ i = i then (1 : ℝ) else 0) - Z (σ i) i| ≤
        |(if σ i = i then (1 : ℝ) else 0)| + |Z (σ i) i| := abs_sub _ _
      _ ≤ 1 + 1 := by
          refine add_le_add ?_ ((hZ _ _).trans h1)
          split_ifs <;> simp
      _ = 2 := by norm_num
  have others : ∀ σ ∈ univ.erase (1 : Equiv.Perm (Fin d)),
      |Equiv.Perm.sign σ • ∏ i, (1 - Z) (σ i) i| ≤ 2 ^ d * ε := by
    intro σ hσ
    have ne : σ ≠ 1 := ne_of_mem_erase hσ
    obtain ⟨i0, hi0⟩ : ∃ i, σ i ≠ i := by
      by_contra h
      push Not at h
      exact ne (Equiv.ext h)
    have small : |(1 - Z) (σ i0) i0| ≤ ε := by
      rw [entry]
      simp only [hi0, ↓reduceIte, zero_sub, abs_neg]
      exact hZ _ _
    have sgn : |Equiv.Perm.sign σ • ∏ i, (1 - Z) (σ i) i| = |∏ i, (1 - Z) (σ i) i| := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [sgn, ← mul_prod_erase _ _ (mem_univ i0), abs_mul, abs_prod]
    have rest : ∏ i ∈ univ.erase i0, |(1 - Z) (σ i) i| ≤ 2 ^ d := by
      calc ∏ i ∈ univ.erase i0, |(1 - Z) (σ i) i| ≤ ∏ i ∈ univ.erase i0, (2 : ℝ) :=
            prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => bounded σ i)
        _ = 2 ^ (univ.erase i0).card := prod_const 2
        _ ≤ 2 ^ d := by
            apply pow_le_pow_right₀ (by norm_num)
            rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
            exact Nat.sub_le d 1
    calc |(1 - Z) (σ i0) i0| * ∏ i ∈ univ.erase i0, |(1 - Z) (σ i) i| ≤ ε * 2 ^ d :=
          mul_le_mul small rest (prod_nonneg fun i _ => abs_nonneg _) h0
      _ = 2 ^ d * ε := mul_comm _ _
  have sumBound : |∑ σ ∈ univ.erase (1 : Equiv.Perm (Fin d)),
      Equiv.Perm.sign σ • ∏ i, (1 - Z) (σ i) i| ≤ d.factorial * (2 ^ d * ε) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum others).trans ?_
    rw [sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : (univ.erase (1 : Equiv.Perm (Fin d))).card ≤ d.factorial := by
      calc (univ.erase (1 : Equiv.Perm (Fin d))).card ≤ (univ : Finset (Equiv.Perm (Fin d))).card :=
            card_erase_le
        _ = d.factorial := by rw [card_univ, Fintype.card_perm, Fintype.card_fin]
    exact_mod_cast this
  have split : Equiv.Perm.sign (1 : Equiv.Perm (Fin d)) • ∏ i, (1 - Z) ((1 : Equiv.Perm (Fin d)) i) i +
      ∑ σ ∈ univ.erase 1, Equiv.Perm.sign σ • ∏ i, (1 - Z) (σ i) i - 1 =
      (Equiv.Perm.sign (1 : Equiv.Perm (Fin d)) • ∏ i, (1 - Z) ((1 : Equiv.Perm (Fin d)) i) i - 1) +
      ∑ σ ∈ univ.erase 1, Equiv.Perm.sign σ • ∏ i, (1 - Z) (σ i) i := by ring
  rw [split]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ d * 2 ^ d * ε + d.factorial * (2 ^ d * ε) := add_le_add identity sumBound
    _ = (d * 2 ^ d + d.factorial * 2 ^ d) * ε := by ring

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Sylvester's identity for endomorphisms. -/
theorem det_one_sub_comp_comm (f g : V →ₗ[ℝ] V) :
    LinearMap.det (1 - f ∘ₗ g) = LinearMap.det (1 - g ∘ₗ f) := by
  let b := Module.finBasis ℝ V
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b, map_sub, map_sub,
    LinearMap.toMatrix_one, LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b,
    Matrix.det_one_sub_mul_comm]

/-- Determinants of small perturbations of the identity. -/
theorem exists_det_bound : ∃ L r : ℝ, 0 < L ∧ 0 < r ∧ ∀ Z : V →L[ℝ] V, ‖Z‖ ≤ r →
    |LinearMap.det (1 - (Z : V →ₗ[ℝ] V)) - 1| ≤ L * ‖Z‖ := by
  classical
  let b := Module.finBasis ℝ V
  let d := Module.finrank ℝ V
  let coord : Fin d → V →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  let c : ℝ := ∑ i, ∑ j, ‖coord i‖ * ‖b j‖ + 1
  have hc : 0 < c := by
    have : 0 ≤ ∑ i, ∑ j, ‖coord i‖ * ‖b j‖ :=
      sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    linarith
  let K : ℝ := d * 2 ^ d + d.factorial * 2 ^ d
  have hK : 0 ≤ K := by positivity
  refine ⟨K * c + 1, c⁻¹, by positivity, inv_pos.mpr hc, fun Z hZ => ?_⟩
  have entries (i j : Fin d) : |LinearMap.toMatrix b b (Z : V →ₗ[ℝ] V) i j| ≤ c * ‖Z‖ := by
    rw [LinearMap.toMatrix_apply]
    have eq : b.repr ((Z : V →ₗ[ℝ] V) (b j)) i = coord i (Z (b j)) := rfl
    rw [eq, ← Real.norm_eq_abs]
    calc ‖coord i (Z (b j))‖ ≤ ‖coord i‖ * (‖Z‖ * ‖b j‖) :=
          (coord i).le_opNorm_of_le (Z.le_opNorm _)
      _ = (‖coord i‖ * ‖b j‖) * ‖Z‖ := by ring
      _ ≤ c * ‖Z‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          have single : ‖coord i‖ * ‖b j‖ ≤ ∑ j', ‖coord i‖ * ‖b j'‖ :=
            single_le_sum (f := fun j' => ‖coord i‖ * ‖b j'‖)
              (fun j' _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mem_univ j)
          have double : ∑ j', ‖coord i‖ * ‖b j'‖ ≤ ∑ i', ∑ j', ‖coord i'‖ * ‖b j'‖ :=
            single_le_sum (f := fun i' => ∑ j', ‖coord i'‖ * ‖b j'‖)
              (fun i' _ => sum_nonneg fun j' _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
              (mem_univ i)
          linarith
  have hε1 : c * ‖Z‖ ≤ 1 := by
    calc c * ‖Z‖ ≤ c * c⁻¹ := mul_le_mul_of_nonneg_left hZ hc.le
      _ = 1 := mul_inv_cancel₀ hc.ne'
  have main := matrix_det_one_sub (LinearMap.toMatrix b b (Z : V →ₗ[ℝ] V)) (c * ‖Z‖)
    (by positivity) hε1 entries
  rw [← LinearMap.det_toMatrix b, map_sub, LinearMap.toMatrix_one]
  calc _ ≤ K * (c * ‖Z‖) := main
    _ ≤ (K * c + 1) * ‖Z‖ := by nlinarith [norm_nonneg Z]

theorem one_sub_ge_exp (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : Real.exp (-(2 * x)) ≤ 1 - x := by
  have pos : 0 < 1 - x := by linarith
  have key : 1 / (1 - x) ≤ Real.exp (2 * x) := by
    calc 1 / (1 - x) ≤ 1 + 2 * x := by
          rw [div_le_iff₀ pos]
          nlinarith
      _ ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
  rw [Real.exp_neg]
  rw [div_le_iff₀ pos, ← div_le_iff₀' (Real.exp_pos _)] at key
  calc (Real.exp (2 * x))⁻¹ = 1 / Real.exp (2 * x) := (one_div _).symm
    _ ≤ 1 - x := key

/-- Products of factors within `x_i ≤ 1/2` of one. -/
theorem prod_bounds {ι : Type*} (s : Finset ι) (f x : ι → ℝ) (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hx1 : ∀ i ∈ s, x i ≤ 1 / 2) (hf : ∀ i ∈ s, |f i - 1| ≤ x i) :
    Real.exp (-(2 * ∑ i ∈ s, x i)) ≤ ∏ i ∈ s, f i ∧ ∏ i ∈ s, f i ≤ Real.exp (∑ i ∈ s, x i) := by
  constructor
  · rw [mul_sum, ← sum_neg_distrib, Real.exp_sum]
    refine prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) (fun i hi => ?_)
    have := one_sub_ge_exp (x i) (hx0 i hi) (hx1 i hi)
    have := (abs_le.mp (hf i hi)).1
    linarith
  · rw [Real.exp_sum]
    refine prod_le_prod₀ (fun i hi => ?_) (fun i hi => ?_)
    · have := (abs_le.mp (hf i hi)).1
      linarith [hx1 i hi]
    · have := (abs_le.mp (hf i hi)).2
      linarith [Real.add_one_le_exp (x i)]

end LeanShared.DeterminantNearOne
