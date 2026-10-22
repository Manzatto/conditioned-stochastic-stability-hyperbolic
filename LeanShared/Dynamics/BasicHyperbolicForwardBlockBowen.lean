module
public import LeanShared.Dynamics.BasicHyperbolicBowenDistortion
public import LeanShared.Dynamics.InvariantCoreHomeomorphism
public import LeanShared.Dynamics.EntireOrbitIdentity
public import LeanShared.Dynamics.ThermodynamicDefinitions

/-! Actual hyperbolic coordinate distortion yields the usual forward
block-orbit energy estimate, with no backward reference orbit in its API. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle NNReal BigOperators

set_option maxHeartbeats 2400000 in
theorem BasicData.forward_block_bowen
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (ψ : M → ℝ) (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ) :
    ∃ N : ℕ, 0 < N ∧ ∃ η > 0, ∃ D ≥ 0,
      ∀ (n : ℕ) (x : Λ) (y : M),
      (∀ j ≤ n, dist (((T : M → M)^[N * j]) x.val) (((T : M → M)^[N * j]) y) < η) →
      |(∑ j ∈ Finset.range (n + 1), ψ (((T : M → M)^[N * j]) x.val)) -
        (∑ j ∈ Finset.range (n + 1), ψ (((T : M → M)^[N * j]) y))| ≤ D := by
  obtain ⟨N, positiveN, η, positiveη, D, nonnegativeD, distortion⟩ :=
    b.block_bowen_distortion forward inverse ψ α positiveα smallα regular
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  have equivariant : Function.Semiconj (Subtype.val : Λ → M) S T := fun _ => rfl
  have powers (m : ℕ) (x : Λ) : ((S ^ m) x).val = (T ^ m) x.val := by
    rw [DiffeomorphismIterates.coe_pow, DiffeomorphismIterates.coe_pow]
    exact (equivariant.iterate_right m).eq x
  refine ⟨N, positiveN, η, positiveη, D, nonnegativeD, ?_⟩
  intro n x y close
  let reference (j : ℤ) := BilateralHomeomorphismOrbit.orbit (S ^ N) x (j - n)
  let orbit (j : ℤ) := BilateralHomeomorphismOrbit.orbit (T ^ N) y (j - n)
  have referenceStep (j : ℤ) : (T ^ N) (reference (j + 1)).val = (reference j).val := by
    rw [← powers]
    change ((S ^ N) (BilateralHomeomorphismOrbit.orbit (S ^ N) x (j + 1 - n))).val = _
    have index : j + 1 - (n : ℤ) = (j - n) + 1 := by omega
    rw [index, BilateralHomeomorphismOrbit.step]
  have orbitStep (j : ℤ) : (T ^ N) (orbit (j + 1)) = orbit j := by
    change (T ^ N) (BilateralHomeomorphismOrbit.orbit (T ^ N) y (j + 1 - n)) = _
    have index : j + 1 - (n : ℤ) = (j - n) + 1 := by omega
    rw [index, BilateralHomeomorphismOrbit.step]
  have referenceValue (j : ℕ) (hj : j ≤ n) :
      (reference j).val = ((T : M → M)^[N * (n - j)]) x.val := by
    have index : (j : ℤ) - n = -((n - j : ℕ) : ℤ) := by omega
    change (BilateralHomeomorphismOrbit.orbit (S ^ N) x ((j : ℤ) - n)).val = _
    rw [index, BilateralHomeomorphismOrbit.pow_neg_nat_time]
    exact (equivariant.iterate_right _).eq x
  have orbitValue (j : ℕ) (hj : j ≤ n) :
      orbit j = ((T : M → M)^[N * (n - j)]) y := by
    have index : (j : ℤ) - n = -((n - j : ℕ) : ℤ) := by omega
    change BilateralHomeomorphismOrbit.orbit (T ^ N) y ((j : ℤ) - n) = _
    rw [index, BilateralHomeomorphismOrbit.pow_neg_nat_time]
  have referenceSum : (∑ j ∈ Finset.range (n + 1), ψ (reference j).val) =
      ∑ j ∈ Finset.range (n + 1), ψ (((T : M → M)^[N * j]) x.val) := by
    calc
      _ = ∑ j ∈ Finset.range (n + 1), ψ (((T : M → M)^[N * (n - j)]) x.val) :=
        Finset.sum_congr rfl (fun j hj => congrArg ψ (referenceValue j (by have := Finset.mem_range.mp hj; omega)))
      _ = _ := by
        simpa only [Nat.add_sub_cancel] using
          Finset.sum_range_reflect (fun j => ψ (((T : M → M)^[N * j]) x.val)) (n + 1)
  have orbitSum : (∑ j ∈ Finset.range (n + 1), ψ (orbit j)) =
      ∑ j ∈ Finset.range (n + 1), ψ (((T : M → M)^[N * j]) y) := by
    calc
      _ = ∑ j ∈ Finset.range (n + 1), ψ (((T : M → M)^[N * (n - j)]) y) :=
        Finset.sum_congr rfl (fun j hj => congrArg ψ (orbitValue j (by have := Finset.mem_range.mp hj; omega)))
      _ = _ := by
        simpa only [Nat.add_sub_cancel] using
          Finset.sum_range_reflect (fun j => ψ (((T : M → M)^[N * j]) y)) (n + 1)
  have estimate := distortion reference referenceStep orbit n (fun j _ => orbitStep j)
    (fun j hj => by rw [referenceValue j hj, orbitValue j hj]; exact close (n - j) (Nat.sub_le _ _))
  rw [referenceSum, orbitSum, abs_sub_comm] at estimate
  exact estimate

end LeanShared.HyperbolicBasicSet
