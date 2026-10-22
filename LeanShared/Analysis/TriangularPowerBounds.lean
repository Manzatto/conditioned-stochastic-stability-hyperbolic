module

public import LeanShared.Analysis.TransientRestriction
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Growth of bounded triangular operators from diagonal power bounds

The diagonal blocks only need geometric power bounds at a positive rate. They need not be mixing and do not need rank-one spectral gaps. Off-diagonal
coupling adds a polynomial factor, which is absorbed at any strictly larger
rate.
-/

@[expose] public noncomputable section

open Finset Filter
open scoped Topology

namespace LeanShared.TriangularPowerBounds

open LeanShared.TransientRestriction

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The standard product norm gives an elementary three-block norm bound. -/
theorem norm_block_le (A : E →L[𝕜] E) (B : E →L[𝕜] F) (D : F →L[𝕜] F) :
    ‖block A B D‖ ≤ ‖A‖ + ‖B‖ + ‖D‖ := by
  have hfst : ‖A.comp (ContinuousLinearMap.fst 𝕜 E F)‖ ≤ ‖A‖ := by
    calc
      _ ≤ ‖A‖ * ‖ContinuousLinearMap.fst 𝕜 E F‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖A‖ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_fst_le 𝕜 E F) (norm_nonneg A)
  have hB : ‖B.comp (ContinuousLinearMap.fst 𝕜 E F)‖ ≤ ‖B‖ := by
    calc
      _ ≤ ‖B‖ * ‖ContinuousLinearMap.fst 𝕜 E F‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖B‖ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_fst_le 𝕜 E F) (norm_nonneg B)
  have hD : ‖D.comp (ContinuousLinearMap.snd 𝕜 E F)‖ ≤ ‖D‖ := by
    calc
      _ ≤ ‖D‖ * ‖ContinuousLinearMap.snd 𝕜 E F‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖D‖ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_snd_le 𝕜 E F) (norm_nonneg D)
  rw [block, ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  apply max_le
  · linarith [norm_nonneg B, norm_nonneg D]
  · have hs := (norm_add_le (B.comp (ContinuousLinearMap.fst 𝕜 E F))
      (D.comp (ContinuousLinearMap.snd 𝕜 E F))).trans (add_le_add hB hD)
    linarith [norm_nonneg A]

/-- The exact off-diagonal convolution in a lower triangular power. -/
theorem powerCoupling_eq_sum (A : E →L[𝕜] E) (B : E →L[𝕜] F) (D : F →L[𝕜] F)
    (n : ℕ) : powerCoupling A B D n =
      ∑ j ∈ range n, (D ^ j).comp (B.comp (A ^ (n - 1 - j))) := by
  induction n with
  | zero => simp [powerCoupling]
  | succ n ih =>
      rw [powerCoupling, ih, ContinuousLinearMap.comp_finsetSum, sum_range_succ']
      have hsum : (∑ j ∈ range n, D.comp ((D ^ j).comp (B.comp (A ^ (n - 1 - j))))) =
          ∑ j ∈ range n, (D ^ (j + 1)).comp (B.comp (A ^ (n + 1 - 1 - (j + 1)))) := by
        apply sum_congr rfl
        intro j _hj
        have hexp : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
        rw [hexp, pow_succ']
        rfl
      rw [hsum]
      simp only [Nat.add_sub_cancel, Nat.sub_zero, pow_zero]
      rw [add_comm]
      rfl

/-- Each convolution term has the same geometric order; there are `n` terms. -/
theorem norm_powerCoupling_le (A : E →L[𝕜] E) (B : E →L[𝕜] F) (D : F →L[𝕜] F)
    {CA CD β : ℝ} (_hCA : 0 ≤ CA) (hCD : 0 ≤ CD) (hβ : 0 ≤ β)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * β ^ n)
    (hD : ∀ n : ℕ, ‖D ^ n‖ ≤ CD * β ^ n) (n : ℕ) :
    ‖powerCoupling A B D n‖ ≤ (n : ℝ) * (CA * CD * ‖B‖) * β ^ (n - 1) := by
  rw [powerCoupling_eq_sum]
  calc
    _ ≤ ∑ j ∈ range n, ‖(D ^ j).comp (B.comp (A ^ (n - 1 - j)))‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range n, CA * CD * ‖B‖ * β ^ (n - 1) := by
      apply sum_le_sum
      intro j hj
      have hcomp : ‖(D ^ j).comp (B.comp (A ^ (n - 1 - j)))‖ ≤
          ‖D ^ j‖ * (‖B‖ * ‖A ^ (n - 1 - j)‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _))
      have hbound : ‖D ^ j‖ * (‖B‖ * ‖A ^ (n - 1 - j)‖) ≤
          (CD * β ^ j) * (‖B‖ * (CA * β ^ (n - 1 - j))) := by
        apply mul_le_mul (hD j)
          (mul_le_mul_of_nonneg_left (hA _) (norm_nonneg B))
          (mul_nonneg (norm_nonneg B) (norm_nonneg _))
          (mul_nonneg hCD (pow_nonneg hβ _))
      apply hcomp.trans (hbound.trans (le_of_eq ?_))
      have hexp : j + (n - 1 - j) = n - 1 := by have := mem_range.mp hj; omega
      calc
        (CD * β ^ j) * (‖B‖ * (CA * β ^ (n - 1 - j))) =
            (CA * CD * ‖B‖) * (β ^ j * β ^ (n - 1 - j)) := by ring
        _ = CA * CD * ‖B‖ * β ^ (n - 1) := by rw [← pow_add, hexp]
    _ = (n : ℝ) * (CA * CD * ‖B‖) * β ^ (n - 1) := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      ring

/-- The complete block power has polynomial-times-geometric growth. -/
theorem norm_block_pow_le (A : E →L[𝕜] E) (B : E →L[𝕜] F) (D : F →L[𝕜] F)
    {CA CD β : ℝ} (hCA : 0 ≤ CA) (hCD : 0 ≤ CD) (hβ : 0 < β)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * β ^ n)
    (hD : ∀ n : ℕ, ‖D ^ n‖ ≤ CD * β ^ n) (n : ℕ) :
    ‖block A B D ^ n‖ ≤
      ((CA + CD) + (n : ℝ) * (CA * CD * ‖B‖ / β)) * β ^ n := by
  rw [block_pow]
  have hC := norm_powerCoupling_le A B D hCA hCD hβ.le hA hD n
  have hexp : (n : ℝ) * (CA * CD * ‖B‖) * β ^ (n - 1) =
      ((n : ℝ) * (CA * CD * ‖B‖ / β)) * β ^ n := by
    cases n with
    | zero => simp
    | succ n =>
        simp only [Nat.add_sub_cancel, pow_succ]
        field_simp
  calc
    _ ≤ ‖A ^ n‖ + ‖powerCoupling A B D n‖ + ‖D ^ n‖ := norm_block_le _ _ _
    _ ≤ CA * β ^ n + ((n : ℝ) * (CA * CD * ‖B‖ / β)) * β ^ n + CD * β ^ n :=
      add_le_add (add_le_add (hA n) (hexp ▸ hC)) (hD n)
    _ = ((CA + CD) + (n : ℝ) * (CA * CD * ‖B‖ / β)) * β ^ n := by ring

/-- Any fixed polynomial factor can be absorbed at an arbitrarily slightly
larger geometric rate. The natural-order exponent is useful for iterated
finite-layer estimates without assuming mixing of the diagonal blocks. -/
theorem exists_geometric_bound_of_polynomial_bound (T : E →L[𝕜] E)
    {a b β γ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hβ : 0 < β) (hβγ : β < γ)
    (m : ℕ) (hT : ∀ n : ℕ, ‖T ^ n‖ ≤ (a + (n : ℝ) ^ m * b) * β ^ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ‖T ^ n‖ ≤ K * γ ^ n := by
  have hγ : 0 < γ := hβ.trans hβγ
  let q := β / γ
  have hq0 : 0 ≤ q := div_nonneg hβ.le hγ.le
  have hq1 : q < 1 := (div_lt_one hγ).mpr hβγ
  have hlim := tendsto_pow_const_mul_const_pow_of_lt_one m hq0 hq1
  obtain ⟨L, hL⟩ := hlim.bddAbove_range
  have hL0 : 0 ≤ L := (mul_nonneg (pow_nonneg (by simp : (0 : ℝ) ≤ 0) m)
    (pow_nonneg hq0 0)).trans (hL ⟨0, by simp⟩)
  refine ⟨a + b * L, add_nonneg ha (mul_nonneg hb hL0), ?_⟩
  intro n
  have heq : q ^ n * γ ^ n = β ^ n := by
    dsimp [q]
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero n hγ.ne')]
  have hpoly : (a + (n : ℝ) ^ m * b) * q ^ n ≤ a + b * L := by
    have hfirst := mul_le_mul_of_nonneg_left (pow_le_one₀ (n := n) hq0 hq1.le) ha
    have hsecond := mul_le_mul_of_nonneg_left (hL ⟨n, rfl⟩) hb
    nlinarith
  calc
    ‖T ^ n‖ ≤ (a + (n : ℝ) ^ m * b) * β ^ n := hT n
    _ = ((a + (n : ℝ) ^ m * b) * q ^ n) * γ ^ n := by rw [mul_assoc, heq]
    _ ≤ (a + b * L) * γ ^ n := mul_le_mul_of_nonneg_right hpoly (pow_nonneg hγ.le n)

/-- Diagonal power growth below a common rate gives block growth at every
strictly larger rate. No simple eigenvalue or mixing condition is required. -/
theorem exists_geometric_block_bound (A : E →L[𝕜] E) (B : E →L[𝕜] F) (D : F →L[𝕜] F)
    {CA CD β γ : ℝ} (hCA : 0 ≤ CA) (hCD : 0 ≤ CD) (hβ : 0 < β) (hβγ : β < γ)
    (hA : ∀ n : ℕ, ‖A ^ n‖ ≤ CA * β ^ n)
    (hD : ∀ n : ℕ, ‖D ^ n‖ ≤ CD * β ^ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ‖block A B D ^ n‖ ≤ K * γ ^ n := by
  apply exists_geometric_bound_of_polynomial_bound (block A B D)
    (add_nonneg hCA hCD) (div_nonneg (mul_nonneg (mul_nonneg hCA hCD) (norm_nonneg B)) hβ.le)
    hβ hβγ 1
  intro n
  simpa only [pow_one] using norm_block_pow_le A B D hCA hCD hβ hA hD n

end LeanShared.TriangularPowerBounds
