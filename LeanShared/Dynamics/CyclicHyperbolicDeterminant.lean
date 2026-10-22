module
public import LeanShared.Dynamics.ForwardHyperbolicSequences
public import LeanShared.Analysis.DeterminantNearOne

/-! Periodic hyperbolic linear products and their Lefschetz determinants. For an
`n`-periodic sequence `M_i = D_i + E_i`, `D_i = A_i × B_i` with `‖A_i⁻¹‖, ‖B_i‖ ≤ k`,
`‖E_i‖ ≤ δ`, `k + δ < 1`, the return product `P = M_{n-1} ⋯ M_0` has `1 - P` injective and
the Green blocks `M_{<j} (1 - P)⁻¹ M_{>j}` are bounded by `C = (k+1)/(1-k-δ)` uniformly in
`n` (forced periodic orbits of the Lyapunov–Perron contraction). Telescoping the
perturbations site by site through Sylvester's identity gives
`det(1 - P_{D+E}) = det(1 - P_D) R` with `exp(-2X) ≤ R ≤ exp X`, `X = L C ∑ ‖E_i‖`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open scoped NNReal
open Finset
namespace LeanShared.CyclicHyperbolicDeterminant

variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

/-- Ordered products `M (a+m-1) ∘ ⋯ ∘ M a`. -/
@[expose] def prodFrom (M : ℤ → (U × S) →L[ℝ] (U × S)) (a : ℤ) :
    ℕ → (U × S) →L[ℝ] (U × S)
  | 0 => ContinuousLinearMap.id ℝ (U × S)
  | m + 1 => (M (a + m)).comp (prodFrom M a m)

theorem prodFrom_zero (M : ℤ → (U × S) →L[ℝ] (U × S)) (a : ℤ) :
    prodFrom M a 0 = ContinuousLinearMap.id ℝ (U × S) := rfl

theorem prodFrom_succ (M : ℤ → (U × S) →L[ℝ] (U × S)) (a : ℤ) (m : ℕ) :
    prodFrom M a (m + 1) = (M (a + m)).comp (prodFrom M a m) := rfl

theorem prodFrom_add (M : ℤ → (U × S) →L[ℝ] (U × S)) (a : ℤ) (m l : ℕ) :
    prodFrom M a (m + l) = (prodFrom M (a + m) l).comp (prodFrom M a m) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [← add_assoc, prodFrom_succ, ih, prodFrom_succ, ContinuousLinearMap.comp_assoc]
    congr 2
    push_cast
    ring

theorem prodFrom_congr (M M' : ℤ → (U × S) →L[ℝ] (U × S)) (a : ℤ) (m : ℕ)
    (h : ∀ l : ℕ, l < m → M (a + l) = M' (a + l)) : prodFrom M a m = prodFrom M' a m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [prodFrom_succ, prodFrom_succ, ih (fun l hl => h l (Nat.lt_succ_of_lt hl)),
      h m (Nat.lt_succ_self m)]

/-- Unforced segments are ordered products. -/
theorem segment (M : ℤ → (U × S) →L[ℝ] (U × S)) (Z W : ℤ → U × S)
    (equation : ∀ i, W (i + 1) = M i (W i) + Z i) (a : ℤ) (m : ℕ)
    (zero : ∀ l : ℕ, l < m → Z (a + l) = 0) : W (a + m) = prodFrom M a m (W a) := by
  induction m with
  | zero => simp only [Nat.cast_zero, add_zero, prodFrom_zero, ContinuousLinearMap.id_apply]
  | succ m ih =>
    have h := equation (a + m)
    rw [zero m (Nat.lt_succ_self m), add_zero, ih (fun l hl => zero l (Nat.lt_succ_of_lt hl))] at h
    rw [Nat.cast_succ, ← add_assoc, h, prodFrom_succ, ContinuousLinearMap.comp_apply]

theorem periodic_mul {X : Type*} (M : ℤ → X) (n : ℕ) (periodic : ∀ i, M (i + n) = M i)
    (i q : ℤ) : M (i + n * q) = M i := by
  have nat : ∀ (j : ℤ) (q : ℕ), M (j + n * q) = M j := by
    intro j q
    induction q with
    | zero => simp only [Nat.cast_zero, mul_zero, add_zero]
    | succ q ih => rw [Nat.cast_succ, mul_add, mul_one, ← add_assoc, periodic, ih]
  rcases Int.eq_nat_or_neg q with ⟨q, rfl | rfl⟩
  · exact nat i q
  · have := nat (i + n * -(q : ℤ)) q
    rw [show i + n * -(q : ℤ) + n * (q : ℤ) = i by ring] at this
    exact this.symm

theorem periodic_emod {X : Type*} (M : ℤ → X) (n : ℕ) (periodic : ∀ i, M (i + n) = M i)
    (i : ℤ) : M (i % n) = M i := by
  conv_rhs => rw [← Int.emod_add_mul_ediv i n]
  exact (periodic_mul M n periodic (i % n) (i / n)).symm

/-- The forward split step equals the forced linear step. -/
theorem step_eq (A : ℤ → U ≃L[ℝ] U) (B : ℤ → S →L[ℝ] S) (M : ℤ → (U × S) →L[ℝ] (U × S))
    (Z : ℤ → U × S) (i : ℤ) (w : U × S) :
    ForwardHyperbolicSequences.step A B
      (fun i w => (M i - (A i : U →L[ℝ] U).prodMap (B i)) w + Z i) i w = M i w + Z i := by
  have split : M i w = ((A i : U →L[ℝ] U).prodMap (B i)) w +
      (M i - (A i : U →L[ℝ] U).prodMap (B i)) w := by
    rw [FunLike.coe_sub, Pi.sub_apply, add_sub_cancel]
  rw [split]
  apply Prod.ext
  · simp only [ForwardHyperbolicSequences.step, ContinuousLinearMap.coe_prodMap', Prod.map_fst,
      Prod.fst_add, add_assoc]
    rfl
  · simp only [ForwardHyperbolicSequences.step, ContinuousLinearMap.coe_prodMap', Prod.map_snd,
      Prod.snd_add, add_assoc]

/-- Forced linear hyperbolic systems: unique bounded solutions. -/
theorem solve (A : ℤ → U ≃L[ℝ] U) (B : ℤ → S →L[ℝ] S) (M : ℤ → (U × S) →L[ℝ] (U × S))
    (k δ : ℝ≥0) (small : k + δ < 1)
    (hA : ∀ i, ‖(A i).symm.toContinuousLinearMap‖ ≤ k) (hB : ∀ i, ‖B i‖ ≤ k)
    (hM : ∀ i, ‖M i - (A i : U →L[ℝ] U).prodMap (B i)‖ ≤ δ)
    (Z : ℤ → U × S) (e : ℝ) (he : ∀ i, ‖Z i‖ ≤ e) :
    ∃ W : ℤ → U × S, (∀ i, W (i + 1) = M i (W i) + Z i) ∧
      (∀ i, ‖W i‖ ≤ (((k : ℝ) + 1) / (1 - (k + δ : ℝ≥0))) * e) ∧
      ∀ W' : ℤ → U × S, (∃ R : ℝ, ∀ i, ‖W' i‖ ≤ R) →
        (∀ i, W' (i + 1) = M i (W' i) + Z i) → W' = W := by
  let N : ℤ → U × S → U × S := fun i w => (M i - (A i : U →L[ℝ] U).prodMap (B i)) w + Z i
  have hN (i : ℤ) : LipschitzWith δ (N i) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [N, dist_add_right]
      exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hM i)).dist_le_mul x y
  have hN0 (i : ℤ) : ‖N i 0‖ ≤ e := by simpa only [N, map_zero, zero_add] using he i
  obtain ⟨W, equation, bound, unique⟩ := ForwardHyperbolicSequences.exists_unique A B N k δ small
    (fun i => ContinuousLinearMap.lipschitzWith_of_opNorm_le (hA i))
    (fun i => ContinuousLinearMap.lipschitzWith_of_opNorm_le (hB i)) hN e hN0
  refine ⟨W, fun i => (equation i).trans (step_eq A B M Z i (W i)), fun i => ?_,
    fun W' bounded eq' => unique W' bounded fun i => (eq' i).trans (step_eq A B M Z i (W' i)).symm⟩
  rw [div_mul_eq_mul_div]
  exact bound i

variable (A : ℤ → U ≃L[ℝ] U) (B : ℤ → S →L[ℝ] S) (M : ℤ → (U × S) →L[ℝ] (U × S))
  (k δ : ℝ≥0)

/-- `1 - P` is injective for periodic hyperbolic products. -/
theorem injective (small : k + δ < 1)
    (hA : ∀ i, ‖(A i).symm.toContinuousLinearMap‖ ≤ k) (hB : ∀ i, ‖B i‖ ≤ k)
    (hM : ∀ i, ‖M i - (A i : U →L[ℝ] U).prodMap (B i)‖ ≤ δ)
    (n : ℕ) (hn : 0 < n) (periodic : ∀ i, M (i + n) = M i) :
    Function.Injective (ContinuousLinearMap.id ℝ (U × S) - prodFrom M 0 n) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  have fixed : prodFrom M 0 n w = w := by
    have := hw
    rw [FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero] at this
    exact this.symm
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  let W : ℤ → U × S := fun i => prodFrom M 0 (i % n).toNat w
  have equation (i : ℤ) : W (i + 1) = M i (W i) + 0 := by
    rw [add_zero]
    have r0 : 0 ≤ i % n := Int.emod_nonneg i hn'.ne'
    have r1 : i % n < n := Int.emod_lt_of_pos i hn'
    have decomposition := Int.emod_add_mul_ediv i n
    rcases lt_or_eq_of_le (show i % n + 1 ≤ n by omega) with lt | eq
    · have next : (i + 1) % n = i % n + 1 := by
        rw [show i + 1 = (i % n + 1) + n * (i / n) by omega, Int.add_mul_emod_self_left,
          Int.emod_eq_of_lt (by omega) lt]
      simp only [W, next]
      rw [show (i % n + 1).toNat = (i % n).toNat + 1 by omega, prodFrom_succ,
        ContinuousLinearMap.comp_apply]
      congr 1
      rw [show (0 : ℤ) + ((i % n).toNat : ℕ) = i % n by omega]
      exact periodic_emod M n periodic i
    · have next : (i + 1) % n = 0 := by
        rw [show i + 1 = n * (i / n + 1) by rw [mul_add, mul_one]; omega]
        exact Int.mul_emod_right _ _
      simp only [W, next, Int.toNat_zero, prodFrom_zero, ContinuousLinearMap.id_apply]
      have last : (i % n).toNat + 1 = n := by omega
      calc w = prodFrom M 0 n w := fixed.symm
        _ = prodFrom M 0 ((i % n).toNat + 1) w := by rw [last]
        _ = M (0 + (((i % n).toNat : ℕ) : ℤ)) (prodFrom M 0 (i % n).toNat w) := by
            rw [prodFrom_succ, ContinuousLinearMap.comp_apply]
        _ = M i (prodFrom M 0 (i % n).toNat w) := by
            rw [show (0 : ℤ) + ((i % n).toNat : ℕ) = i % n by omega, periodic_emod M n periodic i]
  obtain ⟨W0, eq0, _, unique0⟩ := solve A B M k δ small hA hB hM (fun _ => 0) 0
    (fun _ => by rw [norm_zero])
  have bounded : ∃ R : ℝ, ∀ i, ‖W i‖ ≤ R :=
    ⟨∑ m ∈ range n, ‖prodFrom M 0 m w‖, fun i => by
      have r1 : (i % n).toNat < n := by
        have := Int.emod_lt_of_pos i hn'
        have := Int.emod_nonneg i hn'.ne'
        omega
      exact single_le_sum (f := fun m => ‖prodFrom M 0 m w‖) (fun _ _ => norm_nonneg _)
        (mem_range.mpr r1)⟩
  have zeroSolution : (fun _ : ℤ => (0 : U × S)) = W0 :=
    unique0 _ ⟨0, fun _ => le_of_eq norm_zero⟩ (fun i => by simp only [map_zero, add_zero])
  have same : W = W0 := unique0 W bounded equation
  have := congrFun (same.trans zeroSolution.symm) 0
  simpa only [W, Int.zero_emod, Int.toNat_zero, prodFrom_zero,
    ContinuousLinearMap.id_apply] using this

/-- The uniform Green bound. -/
theorem green (small : k + δ < 1)
    (hA : ∀ i, ‖(A i).symm.toContinuousLinearMap‖ ≤ k) (hB : ∀ i, ‖B i‖ ≤ k)
    (hM : ∀ i, ‖M i - (A i : U →L[ℝ] U).prodMap (B i)‖ ≤ δ)
    (n : ℕ) (hn : 0 < n) (periodic : ∀ i, M (i + n) = M i)
    (j : ℕ) (hj : j < n) (z w : U × S)
    (hw : (ContinuousLinearMap.id ℝ (U × S) - prodFrom M 0 n) w =
      prodFrom M (j + 1) (n - j - 1) z) :
    ‖prodFrom M 0 j w‖ ≤ (((k : ℝ) + 1) / (1 - (k + δ : ℝ≥0))) * ‖z‖ := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  let Z : ℤ → U × S := fun i => if i % n = j then z else 0
  obtain ⟨W, equation, bound, unique⟩ := solve A B M k δ small hA hB hM Z ‖z‖
    (fun i => by simp only [Z]; split_ifs <;> simp)
  have periodicW (i : ℤ) : W (i + n) = W i := by
    have shifted := unique (fun i => W (i + n))
      ⟨_, fun i => bound (i + n)⟩ (fun i => by
        have h := equation (i + n)
        rw [show i + n + 1 = i + 1 + n by ring, periodic] at h
        rw [h]
        simp only [Z, Int.add_emod_right])
    exact congrFun shifted i
  have before : W (0 + j) = prodFrom M 0 j (W 0) :=
    segment M Z W equation 0 j (fun l hl => by
      simp only [Z, zero_add]
      rw [ite_eq_right_iff]
      intro h
      rw [Int.emod_eq_of_lt (by omega) (by omega)] at h
      omega)
  have at_j : W ((j : ℤ) + 1) = M j (W j) + z := by
    rw [equation]
    simp only [Z, Int.emod_eq_of_lt (show (0 : ℤ) ≤ j by omega) (show (j : ℤ) < n by omega),
      ↓reduceIte]
  have after : W ((j + 1 : ℤ) + ((n - j - 1 : ℕ) : ℤ)) =
      prodFrom M (j + 1) (n - j - 1) (W (j + 1)) :=
    segment M Z W equation (j + 1) (n - j - 1) (fun l hl => by
      simp only [Z]
      rw [ite_eq_right_iff]
      intro h
      rw [Int.emod_eq_of_lt (by omega) (by omega)] at h
      omega)
  have total : ((j + 1 : ℤ) + ((n - j - 1 : ℕ) : ℤ)) = 0 + n := by
    push_cast [Nat.sub_sub, Nat.cast_sub (show j + 1 ≤ n by omega)]
    ring
  rw [total, periodicW, at_j] at after
  rw [zero_add] at before
  have product : prodFrom M 0 n = (prodFrom M (j + 1) (n - j - 1)).comp
      ((M j).comp (prodFrom M 0 j)) := by
    have h := prodFrom_add M 0 (j + 1) (n - j - 1)
    rw [show j + 1 + (n - j - 1) = n by omega] at h
    rw [h, prodFrom_succ]
    simp only [zero_add, Nat.cast_add, Nat.cast_one]
  have identity : (ContinuousLinearMap.id ℝ (U × S) - prodFrom M 0 n) (W 0) =
      prodFrom M (j + 1) (n - j - 1) z := by
    rw [FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.id_apply, product,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← before]
    conv_lhs => rw [after]
    rw [map_add]
    abel
  have equal : W 0 = w :=
    injective A B M k δ small hA hB hM n hn periodic (identity.trans hw.symm)
  rw [← equal, ← before]
  exact bound j

end LeanShared.CyclicHyperbolicDeterminant
