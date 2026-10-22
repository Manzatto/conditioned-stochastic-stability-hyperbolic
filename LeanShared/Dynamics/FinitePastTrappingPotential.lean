module
public import LeanShared.Dynamics.RobustFiniteIsolation
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! A finite weighted distance to past iterates gives a continuous trapping
potential. The one-step contraction retains the actual homeomorphism. -/
public noncomputable section
open Set Function Metric
namespace LeanShared.FinitePastTrappingPotential
variable {X : Type*} [MetricSpace X] (T : X ≃ₜ X) (K : Set X)

def potential (N : ℕ) (x : X) : ℝ :=
  ∑ j∈Finset.range (N+1), (1/2 : ℝ)^j * infDist ((T.symm : X → X)^[j] x) K

theorem nonnegative (N : ℕ) (x : X) : 0≤potential T K N x :=
  Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg (by norm_num) j) infDist_nonneg

theorem continuous (N : ℕ) : Continuous (potential T K N) := by
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul ((continuous_infDist_pt K).comp (T.symm.continuous.iterate j))

theorem zero_iff (closed : IsClosed K) (nonempty : K.Nonempty) (N : ℕ) (x : X) :
    potential T K N x=0 ↔ x∈finiteForwardCore T.symm K N := by
  constructor
  · intro zero j bound
    have term := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_ : k∈Finset.range (N+1)) =>
        mul_nonneg (pow_nonneg (by norm_num : 0≤(1/2 : ℝ)) k) infDist_nonneg)).mp zero
      j (Finset.mem_range.mpr (by omega))
    exact (closed.mem_iff_infDist_zero nonempty).mpr
      ((mul_eq_zero.mp term).resolve_left (pow_ne_zero j (by norm_num)))
  · intro trapped
    apply Finset.sum_eq_zero
    intro j member
    rw [infDist_zero_of_mem (trapped j (by have := Finset.mem_range.mp member; omega)),mul_zero]

theorem contracts (N : ℕ) {x : X} (inside : T x∈K) :
    potential T K N (T x) ≤ (1/2 : ℝ)*potential T K N x := by
  unfold potential
  rw [Finset.sum_range_succ']
  simp only [iterate_zero,id_eq,pow_zero,one_mul,infDist_zero_of_mem inside,add_zero]
  calc
    ∑ j∈Finset.range N, (1/2 : ℝ)^(j+1)*infDist ((T.symm : X → X)^[j+1] (T x)) K =
        (1/2 : ℝ)*∑ j∈Finset.range N, (1/2 : ℝ)^j*infDist ((T.symm : X → X)^[j] x) K := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [iterate_succ_apply,T.symm_apply_apply,pow_succ]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Finset.sum_range_succ]
      exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (by norm_num) _) infDist_nonneg)
end LeanShared.FinitePastTrappingPotential
