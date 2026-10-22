module

public import LeanShared.Dynamics.FiniteCodingPeriodicWeightComparison
public import LeanShared.Dynamics.CompactInvariantPeriodicGrowth

/-! Direct periodic counting turns the actual higher-image pressure gap
into a strictly smaller exponential error between coding and base sums.
This uses original periodic fibers and does not assume pressure invariance
under a finite-to-one symbolic extension.
-/

public noncomputable section
namespace LeanShared.FiniteCodingManning
open Set Function MeasureTheory BilateralShadowingCoding MarkovFinitePathRealization ThermodynamicDefinitions
open scoped BoundedContinuousFunction
variable {A X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace A] [Fintype A] [DecidableEq A]

theorem periodic_weight_exponential_error (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) (rectangles : A → Set X) (code : Path (Transition T rectangles) → X)
    (properties : FiniteCodingGeometry T rectangles code)
    (gap : (higherMatchingImage T rectangles code).Nonempty →
      pressure T φ (higherMatchingImage T rectangles code) < pressure T φ univ) :
    ∃ P : ℝ, pressure T φ univ = (P : EReal) ∧ ∃ β C : ℝ,
      0 < β ∧ β < Real.exp P ∧ 0 < C ∧ ∀ n : ℕ, ∀ s : Finset X,
        (∀ x, x ∈ s ↔ (T : X → X)^[n + 1] x = x) →
        |bilateralPeriodicWeightSum (φ ∘ code) (n + 1) - ∑ x ∈ s, Real.exp (orbitSum T φ (n + 1) x)| ≤
          C * β ^ (n + 1) := by
  classical
  obtain ⟨P, pressureP⟩ := finite_pressure_of_expansive T c positiveC expansive φ φ.continuous
  let K := higherMatchingImage T rectangles code
  by_cases nonemptyK : K.Nonempty
  · obtain ⟨Q, pressureQ, growth⟩ := actual_periodic_weight_growth_on_invariant T K
      (higherMatchingImage_compact T rectangles code properties) nonemptyK
      (higherMatchingImage_invariant T rectangles code properties) c positiveC
      (fun x _ y _ => expansive x y) φ φ.continuous.continuousOn
    have strict := gap nonemptyK
    rw [pressureP, pressureQ] at strict
    have strictReal : Q < P := EReal.coe_lt_coe_iff.mp strict
    let η := (P - Q) / 2
    have positiveη : 0 < η := by dsimp [η]; linarith
    obtain ⟨C, positive, bound⟩ := growth η positiveη
    refine ⟨P, pressureP, Real.exp (Q + η), ((Fintype.card A : ℝ) ^ 2 + 1) * C,
      Real.exp_pos _, Real.exp_lt_exp.mpr (by dsimp [η]; linarith), by positivity, ?_⟩
    intro n s complete
    have comparison := periodic_weight_comparison T rectangles code properties φ (n + 1) s complete
    have inside : ∀ x ∈ periodicHigherSubset T rectangles code s, x ∈ K := by
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    have fixed : ∀ x ∈ periodicHigherSubset T rectangles code s, (T : X → X)^[n + 1] x = x := by
      intro x hx
      exact (complete x).mp (Finset.mem_filter.mp hx).1
    have periodicBound := bound (n + 1) (by omega) _ inside fixed
    apply comparison.trans
    calc
      _ ≤ ((Fintype.card A : ℝ) ^ 2 + 1) * (C * Real.exp (Q + η) ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left periodicBound (by positivity)
      _ = _ := by ring
  · have emptyK : K = ∅ := Set.not_nonempty_iff_eq_empty.mp nonemptyK
    refine ⟨P, pressureP, Real.exp P / 2, 1, by positivity, by nlinarith [Real.exp_pos P], by norm_num, ?_⟩
    intro n s complete
    have emptyFiltered : periodicHigherSubset T rectangles code s = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      have inside : x ∈ K := (Finset.mem_filter.mp hx).2
      rw [emptyK] at inside
      exact inside
    have comparison := periodic_weight_comparison T rectangles code properties φ (n + 1) s complete
    rw [emptyFiltered, Finset.sum_empty, mul_zero] at comparison
    exact comparison.trans (by positivity)

end LeanShared.FiniteCodingManning
