module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Tactic.Ring

/-! Uniform exponential window variation of an actually summable series.
A head estimate at scale 3m and a geometric tail give a block-m bound;
the possible head length is absorbed by a finite geometric sum.
-/

public noncomputable section
namespace LeanShared.GeometricSeriesWindowVariation
variable {P : Type*}

theorem exists_bound (f : ℕ → P → ℝ) (agreement : ℕ → P → P → Prop) (C θ : ℝ)
    (nonnegativeC : 0 ≤ C) (positiveθ : 0 < θ) (smallθ : θ < 1)
    (uniform : ∀ n a, ‖f n a‖ ≤ C * θ ^ n)
    (head : ∀ m a b, agreement m a b → ∀ n < m, ‖f n b - f n a‖ ≤ 2 * C * θ ^ (2 * m)) :
    ∃ D ≥ 0, ∀ m a b, agreement m a b →
      ‖(∑' n : ℕ, f n b) - ∑' n : ℕ, f n a‖ ≤ D * θ ^ m := by
  have geometric : Summable (fun n : ℕ => θ ^ n) := summable_geometric_of_lt_one positiveθ.le smallθ
  let G := ∑' n : ℕ, θ ^ n
  have nonnegativeG : 0 ≤ G := tsum_nonneg (fun n => pow_nonneg positiveθ.le n)
  have summable (a : P) : Summable (fun n => f n a) :=
    Summable.of_norm_bounded (geometric.mul_left C) (fun n => uniform n a)
  have lengthBound (m : ℕ) : (m : ℝ) * θ ^ m ≤ G := by
    calc
      _ = ∑ _n ∈ Finset.range m, θ ^ m := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ n ∈ Finset.range m, θ ^ n := by
        apply Finset.sum_le_sum
        intro n inside
        exact pow_le_pow_of_le_one positiveθ.le smallθ.le (Nat.le_of_lt (Finset.mem_range.mp inside))
      _ ≤ G := geometric.sum_le_tsum _ (fun n _ => pow_nonneg positiveθ.le n)
  refine ⟨4 * C * G, by positivity, ?_⟩
  intro m a b matching
  let delta := fun n => f n b - f n a
  have split := ((summable b).sub (summable a)).sum_add_tsum_nat_add m
  have difference : (∑' n : ℕ, f n b) - ∑' n : ℕ, f n a =
      (∑ n ∈ Finset.range m, delta n) + ∑' j : ℕ, delta (j + m) :=
    ((summable b).tsum_sub (summable a)).symm.trans split.symm
  have headBound : ‖∑ n ∈ Finset.range m, delta n‖ ≤ (2 * C * θ ^ m) * G := by
    calc
      _ ≤ ∑ n ∈ Finset.range m, ‖delta n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range m, 2 * C * θ ^ (2 * m) :=
        Finset.sum_le_sum (fun n hn => head m a b matching n (Finset.mem_range.mp hn))
      _ = (2 * C * θ ^ m) * ((m : ℝ) * θ ^ m) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, two_mul, pow_add]
        ring
      _ ≤ (2 * C * θ ^ m) * G :=
        mul_le_mul_of_nonneg_left (lengthBound m) (by positivity)
  have tailBound : ‖∑' j : ℕ, delta (j + m)‖ ≤ (2 * C * θ ^ m) * G := by
    apply tsum_of_norm_bounded (geometric.hasSum.mul_left (2 * C * θ ^ m))
    intro j
    calc
      _ ≤ ‖f (j + m) b‖ + ‖f (j + m) a‖ := norm_sub_le _ _
      _ ≤ C * θ ^ (j + m) + C * θ ^ (j + m) := add_le_add (uniform _ b) (uniform _ a)
      _ = (2 * C * θ ^ m) * θ ^ j := by rw [pow_add]; ring
  rw [difference]
  exact (norm_add_le _ _).trans ((add_le_add headBound tailBound).trans_eq (by ring))

end LeanShared.GeometricSeriesWindowVariation
