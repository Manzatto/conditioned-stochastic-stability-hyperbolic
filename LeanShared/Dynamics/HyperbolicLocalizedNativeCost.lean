module
public import LeanShared.Dynamics.HyperbolicNativeUnstablePressureCost
public import LeanShared.Dynamics.HyperbolicPotentialContinuity
public import LeanShared.Geometry.FiniteCaptureWordSupremumCost
public import LeanShared.Analysis.BowenOpenCoverCoefficient

/-! Actual finite-cylinder native principal costs on the core are bounded
by the literal thermodynamic orbit energy. The sum of labelwise suprema
has arbitrarily small exponential loss, uniformly before every length. -/
@[expose] public noncomputable section
namespace LeanShared.HyperbolicBasicSet.HyperbolicData
open Set IsManifold Bundle ThermodynamicDefinitions FiniteSmoothCapturePartition PressureCoverRefinement
open scoped Manifold ContDiff BigOperators
attribute [local instance] Classical.propDecidable
variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype I]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {v : I → Set M}

def localizedNativeCost (h : HyperbolicData (E := E) T Λ)
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ v) (g : M → ℝ)
    (N : ℕ) (labels : Fin (N+1) → I) (y : M) : ℝ :=
  wordCutoff d (fun j => (T : M → M)^[j.val] y) labels *
    ((∏ j ∈ Finset.range N, g ((T : M → M)^[j] y)) / h.nativePressureJacobian N y)

theorem exists_localized_native_cost_radius (h : HyperbolicData (E := E) T Λ)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (g : M → ℝ) (continuous : ContinuousOn g Λ) (positive : ∀ x ∈ Λ, 0 < g x)
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ v) (capture : Λ ⊆ d.capture)
    {δ : ℝ} (positiveδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ N : ℕ, ∀ x ∈ Λ,
      (∑ labels : Fin (N+1) → I,
        domainCoefficient Λ (BowenOpenCoverCoefficient.orbitBall T (N+1) ρ x)
          (h.localizedNativeCost d g N labels)) ≤
      Real.exp (δ * (N+1)) * Real.exp ((N : ℝ) * δ) *
        Real.exp (orbitSum T (h.potential g) N x) := by
  have differential := forward.mdifferentiable one_ne_zero
  have continuousPotential := h.continuousOn_potential forward inverse g continuous positive
  obtain ⟨ρ₀,positiveρ₀,cutoffBudget⟩ := d.exists_word_cost_radius positiveδ
  obtain ⟨ρ₁,positiveρ₁,variation⟩ := Metric.uniformContinuousOn_iff.mp
    (h.compact.uniformContinuousOn_of_continuous continuousPotential) δ positiveδ
  have invariant : MapsTo T Λ Λ := image_subset_iff.mp h.invariant.subset
  refine ⟨min ρ₀ ρ₁,lt_min positiveρ₀ positiveρ₁,fun N x hx => ?_⟩
  let center : Fin (N+1) → M := fun j => (T : M → M)^[j.val] x
  let cell := BowenOpenCoverCoefficient.orbitBall T (N+1) (min ρ₀ ρ₁) x
  let A : M → ℝ := fun y =>
    (∏ j ∈ Finset.range N, g ((T : M → M)^[j] y)) / h.nativePressureJacobian N y
  let B := Real.exp (orbitSum T (h.potential g) N x + (N : ℝ)*δ)
  have tracking (y : M) (hy : y ∈ Λ ∩ cell) (j : Fin (N+1)) :
      dist (center j) ((T : M → M)^[j.val] y) < ρ₀ := by
    rw [dist_comm]
    exact (hy.2 j.val j.isLt).trans_le (min_le_left _ _)
  have bound (y : M) (hy : y ∈ Λ ∩ cell) : A y ≤ B := by
    dsimp only [A,B]
    rw [h.native_weight_div_jacobian differential inverse g positive N y hy.1]
    apply Real.exp_le_exp.mpr
    have each (j : ℕ) (hj : j ∈ Finset.range N) :
        h.potential g ((T : M → M)^[j] y) ≤ h.potential g ((T : M → M)^[j] x) + δ := by
      have close := (hy.2 j (Nat.lt_succ_of_lt (Finset.mem_range.mp hj))).trans_le (min_le_right _ _)
      have small := variation _ (invariant.iterate j hy.1) _ (invariant.iterate j hx) close
      rw [Real.dist_eq] at small
      have upper := (abs_lt.mp small).2
      linarith
    have total := Finset.sum_le_sum each
    simpa only [orbitSum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] using total
  have cost := cutoffBudget (N+1) center (fun j => capture (invariant.iterate j.val hx))
    Λ cell (fun j y => (T : M → M)^[j.val] y) A B (Real.exp_nonneg _) tracking bound
  change (∑ labels : Fin (N+1) → I, domainCoefficient Λ cell
    (fun y => wordCutoff d (fun j => (T : M → M)^[j.val] y) labels * A y)) ≤ _
  apply cost.trans_eq
  dsimp only [B]
  simp only [Nat.cast_add,Nat.cast_one]
  rw [Real.exp_add]
  ring

end LeanShared.HyperbolicBasicSet.HyperbolicData
