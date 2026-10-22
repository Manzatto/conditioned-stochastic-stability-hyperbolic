module

public import LeanShared.Dynamics.HyperbolicUnstableJacobian
public import LeanShared.Geometry.DiffeomorphismIterates
public import LeanShared.Geometry.LinearEquivNormDetCocycle

/-! The actual iterated unstable differential is constructed by composing
the genuine varying-fiber differentials. Its norm determinant is exactly
the product of the literal one-step unstable Jacobians. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}
namespace HyperbolicData

@[expose] def cocyclePoint (T : M ≃ₜ M) (x : M) : ℕ → M
  | 0 => x
  | n + 1 => T (cocyclePoint T x n)

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem cocyclePoint_eq_iterate (T : M ≃ₜ M) (x : M) (n : ℕ) :
    cocyclePoint T x n = (T : M → M)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cocyclePoint, Function.iterate_succ_apply', ih]

omit [FiniteDimensional ℝ E] in
theorem cocyclePoint_mem (h : HyperbolicData (E := E) T Λ) (x : M) (hx : x ∈ Λ) (n : ℕ) :
    cocyclePoint T x n ∈ Λ := by
  rw [cocyclePoint_eq_iterate]
  have invariant : MapsTo (T : M → M) Λ Λ := image_subset_iff.mp h.invariant.subset
  exact invariant.iterate n hx

@[expose] def unstableStep (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (x : M) (hx : x ∈ Λ) (n : ℕ) :
    h.unstable (cocyclePoint T x n) ≃L[ℝ] h.unstable (cocyclePoint T x (n + 1)) :=
  h.unstableDifferential forward inverse (cocyclePoint T x n) (cocyclePoint_mem h x hx n)

@[expose] def unstableCocycle (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (x : M) (hx : x ∈ Λ) (n : ℕ) :
    h.unstable x ≃L[ℝ] h.unstable (cocyclePoint T x n) :=
  LinearEquivNormDetCocycle.product (unstableStep h forward inverse x hx) n

theorem unstableCocycle_normDet (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (x : M) (hx : x ∈ Λ) (n : ℕ) :
    (unstableCocycle h forward inverse x hx n).toLinearMap.normDet =
      ∏ j ∈ Finset.range n, h.unstableJacobian ((T : M → M)^[j] x) := by
  have formula := LinearEquivNormDetCocycle.normDet_product
    (F := fun k => h.unstable (cocyclePoint T x k)) (unstableStep h forward inverse x hx) n
  apply formula.trans
  apply Finset.prod_congr rfl
  intro j _
  rw [← cocyclePoint_eq_iterate T x j]
  exact (h.unstableJacobian_eq_normDet forward inverse (cocyclePoint T x j)
    (cocyclePoint_mem h x hx j)).symm

omit [FiniteDimensional ℝ E] in
set_option maxHeartbeats 1400000 in
theorem unstableCocycle_apply (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (x : M) (hx : x ∈ Λ) (n : ℕ) (v : h.unstable x) :
    (unstableCocycle h forward inverse x hx n v).val =
      mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[n]) x v.val := by
  induction n with
  | zero =>
    change v.val = mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) id x v.val
    rw [mfderiv_id]
    rfl
  | succ n ih =>
    change mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T (cocyclePoint T x n)
      (unstableCocycle h forward inverse x hx n v).val = _
    rw [ih, cocyclePoint_eq_iterate T x n, Function.iterate_succ',
      mfderiv_comp x (forward _) (DiffeomorphismIterates.mdifferentiable_iterate T forward n x)]
    rfl

end HyperbolicData
end LeanShared.HyperbolicBasicSet
