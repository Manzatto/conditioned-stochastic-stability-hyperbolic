module
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Meromorphic.Basic

/-! The resolvent of a genuinely nilpotent operator has an actual finite
Laurent expansion and is meromorphic at zero, including the zero-space case. -/
public noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace LeanShared.NilpotentResolvent
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

@[expose] def laurent (N : A) (n : ℕ) (z : ℂ) : A :=
  ∑ k ∈ Finset.range n, (z⁻¹) ^ (k+1) • N^k

theorem formula (N : A) (n : ℕ) (nilpotent : N^n=0) (z : ℂ) (hz : z ≠ 0) :
    resolvent N z = laurent N n z := by
  let q := z⁻¹ • N
  let G := ∑ k ∈ Finset.range n, q^k
  let B := z⁻¹ • G
  have zeroPower : q^n=0 := by simp only [q, smul_pow, nilpotent, smul_zero]
  have shift : z • (1-q) = algebraMap ℂ A z-N := by
    simp only [q, smul_sub, smul_smul, mul_inv_cancel₀ hz, one_smul,
      Algebra.algebraMap_eq_smul_one]
  have left : (algebraMap ℂ A z-N)*B=1 := by
    rw [←shift]
    dsimp only [B]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hz, one_smul]
    simpa only [G, zeroPower, sub_zero] using mul_neg_geom_sum q n
  have right : B*(algebraMap ℂ A z-N)=1 := by
    rw [←shift]
    dsimp only [B]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hz, one_smul]
    simpa only [G, zeroPower, sub_zero] using geom_sum_mul_neg q n
  have res := spectrum.mem_resolventSet_of_left_right_inverse left right
  have equals : resolvent N z = B :=
    left_inv_eq_right_inv (Ring.inverse_mul_cancel _ res) left
  rw [equals]
  simp only [B, G, laurent, Finset.smul_sum, q, smul_pow, smul_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ']

theorem laurent_meromorphic (N : A) (n : ℕ) : MeromorphicAt (laurent N n) 0 := by
  induction n with
  | zero =>
    have zero : laurent N 0 = fun _ : ℂ => (0 : A) := by
      funext z
      simp only [laurent, Finset.range_zero, Finset.sum_empty]
    rw [zero]
    exact MeromorphicAt.const (0 : A) (0 : ℂ)
  | succ n ih =>
    have term : MeromorphicAt (fun z : ℂ => (z⁻¹)^(n+1) • N^n) 0 :=
      ((MeromorphicAt.id (0 : ℂ)).inv.pow (n+1)).smul (MeromorphicAt.const (N^n) 0)
    have step : laurent N (n+1) = laurent N n + (fun z : ℂ => (z⁻¹)^(n+1) • N^n) := by
      funext z
      exact Finset.sum_range_succ _ n
    rw [step]
    exact ih.add term

theorem meromorphicAt_zero (N : A) (n : ℕ) (nilpotent : N^n=0) :
    MeromorphicAt (fun z : ℂ => resolvent N z) (0 : ℂ) := by
  apply (laurent_meromorphic N n).congr
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (formula N n nilpotent z hz).symm
end LeanShared.NilpotentResolvent
