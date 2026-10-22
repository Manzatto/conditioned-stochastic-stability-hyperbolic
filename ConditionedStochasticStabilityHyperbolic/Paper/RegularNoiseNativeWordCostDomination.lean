module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseNativeWordCostLimit
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Pointwise domination for the actual native costs. Fresh subunit killing
cutoffs and auxiliary subunit terminal cutoffs incur no per-step loss. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
open LeanShared LeanShared.FiniteJetComposition HyperbolicBasicSet FiniteSmoothCapturePartition
variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype I]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {v : I → Set M}

theorem nativeWordCost_nonneg {h : HyperbolicData (E := E) T Λ}
    (a : h.NormedAdaptedProjection) (d : Data (E := E) Λ v) (g : M → ℝ)
    (maps : ℕ → M → M) (N : ℕ) (labels : Fin (N+1) → I) (x : M) :
    0 ≤ nativeWordCost a d g maps N labels x := by
  apply div_nonneg
  · exact mul_nonneg (wordCutoff_nonneg d _ labels) (abs_nonneg _)
  · exact LinearMap.normDet_nonneg _

theorem nativeWordCost_mono {h : HyperbolicData (E := E) T Λ}
    (a : h.NormedAdaptedProjection) (d : Data (E := E) Λ v) (g g' : M → ℝ)
    (dominated : ∀ x, |g' x| ≤ |g x|)
    (maps : ℕ → M → M) (N : ℕ) (labels : Fin (N+1) → I) (x : M) :
    nativeWordCost a d g' maps N labels x ≤ nativeWordCost a d g maps N labels x := by
  have product : |∏ j ∈ Finset.range N, g' (word maps j x)| ≤
      |∏ j ∈ Finset.range N, g (word maps j x)| := by
    rw [Finset.abs_prod,Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun _ _ => dominated _)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left product (wordCutoff_nonneg d _ labels))
    (LinearMap.normDet_nonneg _)

theorem nativeWordCost_killed_le {h : HyperbolicData (E := E) T Λ}
    (a : h.NormedAdaptedProjection) (d : Data (E := E) Λ v) (g χ : M → ℝ)
    (subunit : ∀ x, |χ x| ≤ 1)
    (maps : ℕ → M → M) (N : ℕ) (labels : Fin (N+1) → I) (x : M) :
    nativeWordCost a d (fun x => χ x*g x) maps N labels x ≤
      nativeWordCost a d g maps N labels x := by
  apply nativeWordCost_mono
  intro y
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (subunit y) (abs_nonneg _)).trans_eq (one_mul _)

theorem nativeWordCost_terminal_le {h : HyperbolicData (E := E) T Λ}
    (a : h.NormedAdaptedProjection) (d : Data (E := E) Λ v) (g τ : M → ℝ)
    (subunit : ∀ x, |τ x| ≤ 1)
    (maps : ℕ → M → M) (N : ℕ) (labels : Fin (N+1) → I) (x : M) :
    |τ (word maps N x)| * nativeWordCost a d g maps N labels x ≤
      nativeWordCost a d g maps N labels x :=
  (mul_le_mul_of_nonneg_right (subunit _) (nativeWordCost_nonneg a d g maps N labels x)).trans_eq
    (one_mul _)

theorem nativeWordCost_killed_terminal_le {h : HyperbolicData (E := E) T Λ}
    (a : h.NormedAdaptedProjection) (d : Data (E := E) Λ v) (g χ τ : M → ℝ)
    (killing : ∀ x, |χ x| ≤ 1) (terminal : ∀ x, |τ x| ≤ 1)
    (maps : ℕ → M → M) (N : ℕ) (labels : Fin (N+1) → I) (x : M) :
    |τ (word maps N x)| * nativeWordCost a d (fun x => χ x*g x) maps N labels x ≤
      nativeWordCost a d g maps N labels x :=
  (nativeWordCost_terminal_le a d _ τ terminal maps N labels x).trans
    (nativeWordCost_killed_le a d g χ killing maps N labels x)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
