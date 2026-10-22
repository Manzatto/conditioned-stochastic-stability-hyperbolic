module
public import LeanShared.Geometry.FiniteCaptureWordCutoffs
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! A finite smooth partition admits a uniform inflated product majorant
on orbit tubes. Summing these label majorants costs an arbitrarily small
exponential factor, rather than the number of label words. -/
@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff BigOperators
attribute [local instance] Classical.propDecidable
namespace LeanShared.FiniteSmoothCapturePartition
variable {E M I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [Fintype I] [Fintype J]
  {K : Set M} {v : I → Set M}

def inflatedWordCutoff (d : Data (E := E) K v) (η : ℝ) (points : J → M)
    (labels : J → I) : ℝ := ∏ j, (d.beta (labels j) (points j) + η)

theorem inflatedWordCutoff_sum (d : Data (E := E) K v) (η : ℝ) (points : J → M)
    (capture : ∀ j, points j ∈ d.capture) :
    ∑ labels : J → I, inflatedWordCutoff d η points labels =
      (1 + (Fintype.card I : ℝ) * η) ^ Fintype.card J := by
  classical
  unfold inflatedWordCutoff
  rw [← Fintype.prod_sum (fun j i => d.beta i (points j) + η)]
  have each (j : J) : (∑ i, (d.beta i (points j) + η)) =
      1 + (Fintype.card I : ℝ) * η := by
    rw [Finset.sum_add_distrib,d.one _ (capture j)]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  simp only [each,Finset.prod_const,Finset.card_univ]

theorem wordCutoff_le_inflated (d : Data (E := E) K v) (η : ℝ) (points near : J → M)
    (bound : ∀ j i, d.beta i (near j) ≤ d.beta i (points j) + η) (labels : J → I) :
    wordCutoff d near labels ≤ inflatedWordCutoff d η points labels :=
  Finset.prod_le_prod₀ (fun j _ => (d.bounds (labels j) (near j)).1)
    (fun j _ => bound j (labels j))

theorem inflatedWordCutoff_sum_le (d : Data (E := E) K v) {η δ : ℝ}
    (nonnegative : 0 ≤ η) (budget : 1 + (Fintype.card I : ℝ) * η ≤ Real.exp δ)
    (points : J → M) (capture : ∀ j, points j ∈ d.capture) :
    ∑ labels : J → I, inflatedWordCutoff d η points labels ≤
      Real.exp (δ * Fintype.card J) := by
  rw [inflatedWordCutoff_sum d η points capture]
  calc
    _ ≤ (Real.exp δ) ^ Fintype.card J := pow_le_pow_left₀ (by positivity) budget _
    _ = Real.exp (δ * Fintype.card J) := by rw [← Real.exp_nat_mul,mul_comm]

end LeanShared.FiniteSmoothCapturePartition

open Set IsManifold
open scoped Manifold ContDiff BigOperators
namespace LeanShared.FiniteSmoothCapturePartition
variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype I]
  {K : Set M} {v : I → Set M}

theorem Data.exists_inflated_word_budget (d : Data (E := E) K v)
    {δ : ℝ} (positive : 0 < δ) :
    ∃ η ρ : ℝ, 0 < η ∧ 0 < ρ ∧
      1 + (Fintype.card I : ℝ) * η ≤ Real.exp δ ∧
      (∀ x y : M, dist x y < ρ → ∀ i, d.beta i y ≤ d.beta i x + η) ∧
      ∀ n : ℕ, ∀ points : Fin n → M, (∀ j, points j ∈ d.capture) →
        ∑ labels : Fin n → I, inflatedWordCutoff d η points labels ≤ Real.exp (δ * n) := by
  let η := (Real.exp δ - 1) / ((Fintype.card I : ℝ) + 1)
  have card_nonnegative : 0 ≤ (Fintype.card I : ℝ) := Nat.cast_nonneg _
  have denominator : 0 < (Fintype.card I : ℝ) + 1 := by positivity
  have positiveη : 0 < η := div_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr positive)) denominator
  have normalization : ((Fintype.card I : ℝ) + 1) * η = Real.exp δ - 1 := by
    dsimp only [η]
    rw [mul_div_cancel₀ _ denominator.ne']
  have budget : 1 + (Fintype.card I : ℝ) * η ≤ Real.exp δ := by
    nlinarith
  let values : M → (I → ℝ) := fun x i => d.beta i x
  have continuousValues : Continuous values := continuous_pi (fun i => (d.smooth i).continuous)
  obtain ⟨ρ,positiveρ,variation⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous continuousValues) η positiveη
  refine ⟨η,ρ,positiveη,positiveρ,budget,?_,?_⟩
  · intro x y close i
    have small : dist (d.beta i x) (d.beta i y) < η :=
      (dist_le_pi_dist (values x) (values y) i).trans_lt (variation close)
    rw [Real.dist_eq] at small
    have lower := neg_abs_le (d.beta i x - d.beta i y)
    linarith
  · intro n points capture
    have bound := inflatedWordCutoff_sum_le d positiveη.le budget points capture
    simp only [Fintype.card_fin] at bound
    convert bound using 1
    congr 1
    ext labels
    simp only [Finset.mem_univ]

end LeanShared.FiniteSmoothCapturePartition
