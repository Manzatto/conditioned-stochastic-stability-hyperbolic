module
public import LeanShared.Dynamics.HyperbolicAdaptedForms

/-! Uniform comparison at every fixed adapted time, so a time selected for
one-step contraction is retained by the atlas and frame constructions. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
namespace LeanShared.HyperbolicAdaptedUniformComparison
open HyperbolicAdaptedForms HyperbolicFiniteAdaptedEnergy
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

theorem energy_upper (f : M → M) (a C q : ℝ) (N : ℕ)
    (x : M) (v : TangentSpace (𝓘(ℝ, E)) x)
    (bound : ∀ j : ℕ,
      ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[j]) x v‖ ≤ C * q ^ j * ‖v‖) :
    iterateEnergy f a N x v ≤
      (∑ j ∈ Finset.range N, ((a ^ 2)⁻¹) ^ j * (C * q ^ j) ^ 2) * ‖v‖ ^ 2 := by
  unfold iterateEnergy FiniteAdaptedEnergy.energy
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have squared := pow_le_pow_left₀ (norm_nonneg _) (bound j) 2
  calc
    _ ≤ ((a ^ 2)⁻¹) ^ j * (C * q ^ j * ‖v‖) ^ 2 :=
      mul_le_mul_of_nonneg_left squared (pow_nonneg (inv_nonneg.mpr (sq_nonneg _)) _)
    _ = _ := by ring

/-- A common global upper constant is derived at the already selected time.
It does not select another terminal time. -/
theorem uniform_comparison [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M}
    (h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ)
    (a : ℝ) (N : ℕ) (length : 0 < N) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Λ, ∀ v : TangentSpace (𝓘(ℝ, E)) x,
      ‖v‖ ^ 2 ≤ 2 * splitForm T T.symm h.projection a N x v v ∧
      splitForm T T.symm h.projection a N x v v ≤ B * ‖v‖ ^ 2 := by
  let K := ∑ j ∈ Finset.range N, ((a ^ 2)⁻¹) ^ j * (h.constant * h.contraction ^ j) ^ 2
  let B := max 1 K
  have hB : 1 ≤ B := le_max_left _ _
  obtain ⟨C, positiveC, bounds⟩ := h.exists_projection_norm_bound
  refine ⟨2 * B * C ^ 2, mul_pos (mul_pos (by norm_num) (by linarith))
    (sq_pos_of_pos positiveC), ?_⟩
  intro x hx v
  refine ⟨splitForm_lower T T.symm h.projection a N length x v, ?_⟩
  have smem : h.projection x v ∈ h.stable x := by
    rw [← h.projection_range x hx]
    exact LinearMap.mem_range.mpr ⟨v, rfl⟩
  have umem : v - h.projection x v ∈ h.unstable x := by
    rw [← h.projection_kernel x hx]
    change h.projection x (v - h.projection x v) = 0
    rw [map_sub, show h.projection x (h.projection x v) = h.projection x v from
      congrArg (fun L => L v) (h.projection_idempotent x hx), sub_self]
  have sp : ‖h.projection x v‖ ≤ C * ‖v‖ :=
    ((h.projection x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (bounds x hx).1 (norm_nonneg _))
  have up : ‖v - h.projection x v‖ ≤ C * ‖v‖ :=
    ((ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ, E)) x) - h.projection x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (bounds x hx).2 (norm_nonneg _))
  have sEnergy := energy_upper T a h.constant h.contraction N x (h.projection x v)
    (fun j => h.stable_bound j x hx _ smem)
  have uEnergy := energy_upper T.symm a h.constant h.contraction N x (v - h.projection x v)
    (fun j => h.unstable_bound j x hx _ umem)
  rw [splitForm_self]
  calc
    _ ≤ K * ‖h.projection x v‖ ^ 2 + K * ‖v - h.projection x v‖ ^ 2 := add_le_add sEnergy uEnergy
    _ ≤ B * ‖h.projection x v‖ ^ 2 + B * ‖v - h.projection x v‖ ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_right 1 K) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (le_max_right 1 K) (sq_nonneg _))
    _ ≤ B * (C * ‖v‖) ^ 2 + B * (C * ‖v‖) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) sp 2) (by linarith))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) up 2) (by linarith))
    _ = _ := by ring

end LeanShared.HyperbolicAdaptedUniformComparison
