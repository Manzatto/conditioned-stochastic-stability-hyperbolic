module
public import LeanShared.Dynamics.CyclicHyperbolicDeterminant

/-! Site-by-site telescoping of Lefschetz determinants of periodic hyperbolic
products. Adding a perturbation `E'` at one site `j` multiplies `det(1 - P)` by
`det(1 - G E')`, where `G = M_{<j} (1 - P)⁻¹ M_{>j}` is a Green block bounded by `C`
(Sylvester's identity). Hence `det(1 - P_{D+E}) = det(1 - P_D) R` with
`exp(-2X) ≤ R ≤ exp X`, `X = L C ∑_{i<n} ‖E_i‖`, uniformly in the period. -/
public noncomputable section
set_option linter.unusedSectionVars false
open scoped NNReal
open Finset
namespace LeanShared.CyclicHyperbolicDeterminant

variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

/-- The return product splits at a site. -/
theorem prodFrom_split (M : ℤ → (U × S) →L[ℝ] (U × S)) (n j : ℕ) (hj : j < n) :
    prodFrom M 0 n = (prodFrom M (j + 1) (n - j - 1)).comp ((M j).comp (prodFrom M 0 j)) := by
  have h := prodFrom_add M 0 (j + 1) (n - j - 1)
  rw [show j + 1 + (n - j - 1) = n by omega] at h
  rw [h, prodFrom_succ]
  simp only [zero_add, Nat.cast_add, Nat.cast_one]

/-- Changing one site of the return product. -/
theorem prodFrom_single (M M' : ℤ → (U × S) →L[ℝ] (U × S)) (n j : ℕ) (hj : j < n)
    (E' : (U × S) →L[ℝ] (U × S))
    (same : ∀ i : ℕ, i < n → i ≠ j → M' i = M i) (changed : M' j = M j + E') :
    prodFrom M' 0 n = (prodFrom M (j + 1) (n - j - 1)).comp ((M j + E').comp (prodFrom M 0 j)) := by
  have hX : prodFrom M' (j + 1) (n - j - 1) = prodFrom M (j + 1) (n - j - 1) :=
    prodFrom_congr M' M (j + 1) (n - j - 1) (fun l hl => by
      have := same (j + 1 + l) (by omega) (by omega)
      rw [show ((j : ℤ) + 1 + (l : ℤ)) = ((j + 1 + l : ℕ) : ℤ) by push_cast; ring]
      exact this)
  have hY : prodFrom M' 0 j = prodFrom M 0 j :=
    prodFrom_congr M' M 0 j (fun l hl => by
      have := same l (by omega) (by omega)
      simpa only [zero_add] using this)
  rw [prodFrom_split M' n j hj, changed, hX, hY]

/-- One-site perturbations multiply the Lefschetz determinant by `det(1 - G E')`. -/
theorem det_single (A : ℤ → U ≃L[ℝ] U) (B : ℤ → S →L[ℝ] S) (M : ℤ → (U × S) →L[ℝ] (U × S))
    (k δ : ℝ≥0) (small : k + δ < 1)
    (hA : ∀ i, ‖(A i).symm.toContinuousLinearMap‖ ≤ k) (hB : ∀ i, ‖B i‖ ≤ k)
    (hM : ∀ i, ‖M i - (A i : U →L[ℝ] U).prodMap (B i)‖ ≤ δ)
    (n : ℕ) (hn : 0 < n) (periodic : ∀ i, M (i + n) = M i) (j : ℕ) (hj : j < n)
    (E' : (U × S) →L[ℝ] (U × S)) :
    ∃ G : (U × S) →L[ℝ] (U × S), ‖G‖ ≤ ((k : ℝ) + 1) / (1 - (k + δ : ℝ≥0)) ∧
      LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) - (prodFrom M (j + 1) (n - j - 1)).comp
        ((M j + E').comp (prodFrom M 0 j))) : (U × S) →ₗ[ℝ] (U × S)) =
      LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) - prodFrom M 0 n) :
        (U × S) →ₗ[ℝ] (U × S)) *
      LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) - G.comp E') : (U × S) →ₗ[ℝ] (U × S)) := by
  set C : ℝ := ((k : ℝ) + 1) / (1 - (k + δ : ℝ≥0))
  have hC : 0 ≤ C := by
    have : ((k + δ : ℝ≥0) : ℝ) < 1 := by exact_mod_cast small
    exact div_nonneg (by positivity) (by linarith)
  set P := prodFrom M 0 n
  set X := prodFrom M (j + 1) (n - j - 1)
  set Y := prodFrom M 0 j
  set Q : (U × S) →ₗ[ℝ] (U × S) := ((ContinuousLinearMap.id ℝ (U × S) - P) : (U × S) →ₗ[ℝ] (U × S))
  have injectiveQ : Function.Injective Q := injective A B M k δ small hA hB hM n hn periodic
  let e : (U × S) ≃ₗ[ℝ] (U × S) := LinearEquiv.ofInjectiveEndo Q injectiveQ
  have eApply (v : U × S) : e v = Q v := rfl
  let Gl : (U × S) →ₗ[ℝ] (U × S) := (Y : (U × S) →ₗ[ℝ] (U × S)) ∘ₗ (e.symm : (U × S) →ₗ[ℝ] (U × S)) ∘ₗ
    (X : (U × S) →ₗ[ℝ] (U × S))
  let G : (U × S) →L[ℝ] (U × S) := LinearMap.toContinuousLinearMap Gl
  have bound : ‖G‖ ≤ C := by
    refine ContinuousLinearMap.opNorm_le_bound _ hC fun z => ?_
    have identity : (ContinuousLinearMap.id ℝ (U × S) - P) (e.symm (X z)) = X z := by
      change Q (e.symm (X z)) = X z
      rw [← eApply, e.apply_symm_apply]
    exact green A B M k δ small hA hB hM n hn periodic j hj z _ identity
  refine ⟨G, bound, ?_⟩
  have split := prodFrom_split M n j hj
  -- 1 - X (M j + E') Y = Q ∘ (1 - e⁻¹ X E' Y)
  have factor : ((ContinuousLinearMap.id ℝ (U × S) - X.comp ((M j + E').comp Y)) :
      (U × S) →ₗ[ℝ] (U × S)) =
      Q ∘ₗ (1 - ((e.symm : (U × S) →ₗ[ℝ] (U × S)) ∘ₗ (X : (U × S) →ₗ[ℝ] (U × S)) ∘ₗ
        (E' : (U × S) →ₗ[ℝ] (U × S))) ∘ₗ (Y : (U × S) →ₗ[ℝ] (U × S))) := by
    apply LinearMap.ext
    intro v
    have inverse : Q (e.symm (X (E' (Y v)))) = X (E' (Y v)) := by
      rw [← eApply, e.apply_symm_apply]
    have product : P v = X (M j (Y v)) := by
      change prodFrom M 0 n v = X (M j (Y v))
      rw [split]
      rfl
    change v - X ((M j + E') (Y v)) = Q (v - e.symm (X (E' (Y v))))
    rw [map_sub, inverse]
    change _ = (v - P v) - X (E' (Y v))
    rw [product, FunLike.coe_add, Pi.add_apply, map_add]
    abel
  rw [factor, LinearMap.det_comp]
  congr 1
  rw [DeterminantNearOne.det_one_sub_comp_comm]
  congr 2

theorem coe_id_sub (Z : (U × S) →L[ℝ] (U × S)) :
    ((ContinuousLinearMap.id ℝ (U × S) - Z : (U × S) →L[ℝ] (U × S)) : (U × S) →ₗ[ℝ] (U × S)) =
      1 - (Z : (U × S) →ₗ[ℝ] (U × S)) :=
  LinearMap.ext fun _ => rfl

/-- Lefschetz determinants of perturbed periodic hyperbolic products, uniformly in the
period: `det(1 - P_{D+E}) = det(1 - P_D) R` with `exp(-2X) ≤ R ≤ exp X`. -/
theorem det_ratio : ∃ L r : ℝ, 0 < L ∧ 0 < r ∧
    ∀ (A : ℤ → U ≃L[ℝ] U) (B : ℤ → S →L[ℝ] S) (E : ℤ → (U × S) →L[ℝ] (U × S))
      (k δ : ℝ≥0) (_ : k + δ < 1)
      (_ : ∀ i, ‖(A i).symm.toContinuousLinearMap‖ ≤ k) (_ : ∀ i, ‖B i‖ ≤ k)
      (_ : ∀ i, ‖E i‖ ≤ δ) (n : ℕ) (_ : 0 < n)
      (_ : ∀ i, A (i + n) = A i) (_ : ∀ i, B (i + n) = B i) (_ : ∀ i, E (i + n) = E i),
      (∀ i, ((k : ℝ) + 1) / (1 - (k + δ : ℝ≥0)) * ‖E i‖ ≤ r) →
      (∀ i, L * (((k : ℝ) + 1) / (1 - (k + δ : ℝ≥0)) * ‖E i‖) ≤ 1 / 2) →
      ∃ R : ℝ,
        LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) -
          prodFrom (fun i => (A i : U →L[ℝ] U).prodMap (B i) + E i) 0 n) :
            (U × S) →ₗ[ℝ] (U × S)) =
        LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) -
          prodFrom (fun i => (A i : U →L[ℝ] U).prodMap (B i)) 0 n) :
            (U × S) →ₗ[ℝ] (U × S)) * R ∧
        Real.exp (-(2 * ∑ i ∈ range n,
          L * (((k : ℝ) + 1) / (1 - (k + δ : ℝ≥0)) * ‖E i‖))) ≤ R ∧
        R ≤ Real.exp (∑ i ∈ range n, L * (((k : ℝ) + 1) / (1 - (k + δ : ℝ≥0)) * ‖E i‖)) := by
  obtain ⟨L, r, hL, hr, detBound⟩ := DeterminantNearOne.exists_det_bound (V := U × S)
  refine ⟨L, r, hL, hr, fun A B E k δ small hA hB hE n hn pA pB pE hEr hEL => ?_⟩
  set C : ℝ := ((k : ℝ) + 1) / (1 - (k + δ : ℝ≥0))
  let D : ℤ → (U × S) →L[ℝ] (U × S) := fun i => (A i : U →L[ℝ] U).prodMap (B i)
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  let Mm : ℕ → ℤ → (U × S) →L[ℝ] (U × S) := fun m i => D i + if i % n < m then E i else 0
  have periodicM (m : ℕ) (i : ℤ) : Mm m (i + n) = Mm m i := by
    simp only [Mm, D, pA, pB, pE, Int.add_emod_right]
  have closeM (m : ℕ) (i : ℤ) : ‖Mm m i - (A i : U →L[ℝ] U).prodMap (B i)‖ ≤ δ := by
    simp only [Mm, D, add_sub_cancel_left]
    split_ifs
    · exact hE i
    · simp only [norm_zero, NNReal.coe_nonneg]
  have zeroM : prodFrom (Mm 0) 0 n = prodFrom D 0 n :=
    prodFrom_congr _ _ 0 n (fun l _ => by
      have h : ¬ ((0 + (l : ℤ)) % n < ((0 : ℕ) : ℤ)) := by
        have := Int.emod_nonneg (0 + (l : ℤ)) hn'.ne'
        push_cast
        omega
      simp only [Mm, h, ↓reduceIte, add_zero])
  have fullM : prodFrom (Mm n) 0 n = prodFrom (fun i => D i + E i) 0 n :=
    prodFrom_congr _ _ 0 n (fun l hl => by
      have h : (0 + (l : ℤ)) % n < (n : ℤ) := by
        rw [Int.emod_eq_of_lt (by omega) (by omega)]
        omega
      simp only [Mm, h, ↓reduceIte])
  have claim : ∀ m : ℕ, m ≤ n → ∃ R : ℝ,
      LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) - prodFrom (Mm m) 0 n) :
        (U × S) →ₗ[ℝ] (U × S)) =
      LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) - prodFrom D 0 n) :
        (U × S) →ₗ[ℝ] (U × S)) * R ∧
      Real.exp (-(2 * ∑ i ∈ range m, L * (C * ‖E i‖))) ≤ R ∧
      R ≤ Real.exp (∑ i ∈ range m, L * (C * ‖E i‖)) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨1, by rw [zeroM, mul_one], ?_, ?_⟩ <;> simp
    | succ m ih =>
      intro hm
      obtain ⟨R, equation, lower, upper⟩ := ih (by omega)
      obtain ⟨G, hG, single⟩ := det_single A B (Mm m) k δ small hA hB (closeM m) n hn
        (periodicM m) m (by omega) (E m)
      have changed := prodFrom_single (Mm m) (Mm (m + 1)) n m (by omega) (E m)
        (fun i hi hne => by
          simp only [Mm]
          have : ((i : ℤ) % n) = i := Int.emod_eq_of_lt (by omega) (by omega)
          rw [this]
          congr 1
          by_cases h : i < m
          · have h1 : (i : ℤ) < ((m + 1 : ℕ) : ℤ) := by push_cast; omega
            have h2 : (i : ℤ) < (m : ℤ) := by omega
            simp only [h1, h2, ↓reduceIte]
          · have h1 : ¬ (i : ℤ) < ((m + 1 : ℕ) : ℤ) := by push_cast; omega
            have h2 : ¬ (i : ℤ) < (m : ℤ) := by omega
            simp only [h1, h2, ↓reduceIte])
        (by
          simp only [Mm]
          have : ((m : ℤ) % n) = m := Int.emod_eq_of_lt (by omega) (by omega)
          have h1 : (m : ℤ) < ((m + 1 : ℕ) : ℤ) := by push_cast; omega
          have h2 : ¬ (m : ℤ) < (m : ℤ) := lt_irrefl _
          simp only [this, h1, h2, ↓reduceIte, add_zero])
      have small_m : ‖G.comp (E m)‖ ≤ C * ‖E m‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right hG (norm_nonneg _))
      have hf : |LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) - G.comp (E m)) :
          (U × S) →ₗ[ℝ] (U × S)) - 1| ≤ L * (C * ‖E m‖) := by
        have := detBound (G.comp (E m)) (small_m.trans (hEr m))
        have e1 : ((ContinuousLinearMap.id ℝ (U × S) : (U × S) →L[ℝ] (U × S)) :
            (U × S) →ₗ[ℝ] (U × S)) = 1 := rfl
        rw [e1]
        exact this.trans (mul_le_mul_of_nonneg_left small_m hL.le)
      set f := LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) - G.comp (E m)) :
        (U × S) →ₗ[ℝ] (U × S))
      have hx0 : 0 ≤ L * (C * ‖E m‖) := (abs_nonneg _).trans hf
      have flow := DeterminantNearOne.one_sub_ge_exp _ hx0 (hEL m)
      have fLower : Real.exp (-(2 * (L * (C * ‖E m‖)))) ≤ f := by
        have := (abs_le.mp hf).1
        linarith
      have fUpper : f ≤ Real.exp (L * (C * ‖E m‖)) := by
        have := (abs_le.mp hf).2
        linarith [Real.add_one_le_exp (L * (C * ‖E m‖))]
      have fpos : 0 ≤ f := (Real.exp_pos _).le.trans fLower
      have Rpos : 0 ≤ R := (Real.exp_pos _).le.trans lower
      refine ⟨R * f, ?_, ?_, ?_⟩
      · rw [changed, single, equation, mul_assoc]
      · rw [sum_range_succ, mul_add, neg_add, Real.exp_add]
        exact mul_le_mul lower fLower (Real.exp_pos _).le Rpos
      · rw [sum_range_succ, Real.exp_add]
        exact mul_le_mul upper fUpper fpos (Real.exp_pos _).le
  obtain ⟨R, equation, lower, upper⟩ := claim n le_rfl
  exact ⟨R, by rw [← fullM]; exact equation, lower, upper⟩

end LeanShared.CyclicHyperbolicDeterminant
