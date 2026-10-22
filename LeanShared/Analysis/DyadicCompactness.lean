module

public import LeanShared.Analysis.CompactnessFromComponents
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Compactness from actual geometrically reweighted blocks

The target is the complete supremum space of block values. Uniformly bounded
compact block operators, reweighted by a geometric factor, construct a compact
operator into that space. The finite-block/tail estimate is proved here.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace LeanShared.DyadicCompactness

/-- The weakening of a dyadic exponent is a genuine geometric factor. -/
def dyadicFactor (η : ℝ) : ℝ := (2 : ℝ) ^ (-η)

theorem dyadicFactor_pos (η : ℝ) : 0 < dyadicFactor η :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem dyadicFactor_lt_one {η : ℝ} (hη : 0 < η) : dyadicFactor η < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hη)

theorem dyadic_weight_ratio (t t' : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (t * n) / (2 : ℝ) ^ (t' * n) = dyadicFactor (t' - t) ^ n := by
  rw [← Real.rpow_sub (by norm_num)]
  unfold dyadicFactor
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

variable {E F S : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  (c : ℕ × S → E →L[ℂ] F) {C θ : ℝ} (hC : 0 ≤ C)
  (hc : ∀ i, ‖c i‖ ≤ C) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)

abbrev BlockSpace := lp (fun _ : ℕ × S => F) ∞

include hC hc hθ hθ1

theorem block_bound (z : E) (i : ℕ × S) :
    ‖((θ ^ i.1 : ℝ) : ℂ) • c i z‖ ≤ C * ‖z‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hθ _)]
  calc
    _ ≤ θ ^ i.1 * (C * ‖z‖) :=
      mul_le_mul_of_nonneg_left ((c i).le_opNorm z |>.trans
        (mul_le_mul_of_nonneg_right (hc i) (norm_nonneg z))) (pow_nonneg hθ _)
    _ ≤ _ := mul_le_of_le_one_left (mul_nonneg hC (norm_nonneg z)) (pow_le_one₀ hθ hθ1)

/-- The actual sequence of weakened block values. -/
def blockValues (z : E) : BlockSpace (F := F) (S := S) :=
  ⟨fun i => ((θ ^ i.1 : ℝ) : ℂ) • c i z,
    memℓp_infty ⟨C * ‖z‖, by
      rintro _ ⟨i, rfl⟩
      exact block_bound c hC hc hθ hθ1 z i⟩⟩

theorem blockValues_norm_le (z : E) :
    ‖blockValues c hC hc hθ hθ1 z‖ ≤ C * ‖z‖ :=
  lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg z))
    (block_bound c hC hc hθ hθ1 z)

/-- Constructed continuous linear reweighting into the block supremum norm. -/
def operator : E →L[ℂ] BlockSpace (F := F) (S := S) :=
  LinearMap.mkContinuous
    { toFun := blockValues c hC hc hθ hθ1
      map_add' := fun x y => by
        apply lp.ext
        funext i
        change ((θ ^ i.1 : ℝ) : ℂ) • c i (x + y) =
          ((θ ^ i.1 : ℝ) : ℂ) • c i x + ((θ ^ i.1 : ℝ) : ℂ) • c i y
        rw [map_add, smul_add]
      map_smul' := fun a z => by
        apply lp.ext
        funext i
        change ((θ ^ i.1 : ℝ) : ℂ) • c i (a • z) =
          a • (((θ ^ i.1 : ℝ) : ℂ) • c i z)
        rw [map_smul, smul_comm] }
    C (blockValues_norm_le c hC hc hθ hθ1)

theorem operator_apply (z : E) (i : ℕ × S) :
    operator c hC hc hθ hθ1 z i = ((θ ^ i.1 : ℝ) : ℂ) • c i z := rfl

variable [Fintype S]

/-- The finite-component and small-tail bound follows from the sequence norm. -/
theorem finite_tail_bound (N : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (hsmall : ∀ n ≥ N, θ ^ n * C ≤ η) (z : E) :
    ‖operator c hC hc hθ hθ1 z‖ ≤
      ‖fun i : (Finset.range N ×ˢ Finset.univ : Finset (ℕ × S)) => c i z‖ + η * ‖z‖ := by
  classical
  apply lp.norm_le_of_forall_le (add_nonneg (norm_nonneg _) (mul_nonneg hη (norm_nonneg z)))
  intro i
  rw [operator_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hθ _)]
  by_cases hi : i.1 < N
  · have himem : i ∈ (Finset.range N ×ˢ Finset.univ : Finset (ℕ × S)) := by
      simp [hi]
    have hb := norm_le_pi_norm (fun j : (Finset.range N ×ˢ Finset.univ : Finset (ℕ × S)) =>
      c j z) ⟨i, himem⟩
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hθ hθ1)).trans
      (hb.trans (le_add_of_nonneg_right (mul_nonneg hη (norm_nonneg z))))
  · have hb : ‖c i z‖ ≤ C * ‖z‖ := (c i).le_opNorm z |>.trans
      (mul_le_mul_of_nonneg_right (hc i) (norm_nonneg z))
    calc
      _ ≤ θ ^ i.1 * (C * ‖z‖) := mul_le_mul_of_nonneg_left hb (pow_nonneg hθ _)
      _ = (θ ^ i.1 * C) * ‖z‖ := (mul_assoc _ _ _).symm
      _ ≤ η * ‖z‖ := mul_le_mul_of_nonneg_right (hsmall _ (Nat.le_of_not_gt hi)) (norm_nonneg z)
      _ ≤ _ := le_add_of_nonneg_left (norm_nonneg _)

/-- Compactness of actual blocks plus strict geometric weakening yields
compactness of the constructed operator. -/
theorem operator_isCompact [CompleteSpace F] (hθlt : θ < 1)
    (hcompact : ∀ i, IsCompactOperator (c i)) :
    IsCompactOperator (operator c hC hc hθ hθ1) := by
  classical
  apply CompactnessFromComponents.isCompactOperator_of_small_tails _ c hcompact
  intro η hη
  have ht : Tendsto (fun n : ℕ => θ ^ n * C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθlt).mul_const C
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hη))
  refine ⟨Finset.range N ×ˢ Finset.univ, 1, zero_le_one, ?_⟩
  intro z
  simpa only [one_mul] using finite_tail_bound c hC hc hθ hθ1 N hη.le
    (fun n hn => (hN n hn).le) z

omit hθ hθ1 in
/-- Strictly reducing both dyadic exponents gives a compact weakened block
operator, once the actual normalized blocks are compact and uniformly bounded. -/
theorem dyadic_operator_isCompact [CompleteSpace F] {η : ℝ} (hη : 0 < η)
    (hcompact : ∀ i, IsCompactOperator (c i)) :
    IsCompactOperator (operator c hC hc (dyadicFactor_pos η).le
      (dyadicFactor_lt_one hη).le) :=
  operator_isCompact c hC hc (dyadicFactor_pos η).le
    (dyadicFactor_lt_one hη).le (dyadicFactor_lt_one hη) hcompact

end LeanShared.DyadicCompactness
