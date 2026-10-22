module

public import LeanShared.Dynamics.HyperbolicUnstableReturn
public import LeanShared.Geometry.DiffeomorphismInverseDifferential

/-! The actual inverse unstable periodic return is the derivative of the
literal inverse iterate. Its contraction bound follows from the standing
hyperbolic bound with exact native fiber norm transport. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}
namespace HyperbolicData

omit [FiniteDimensional ℝ E] in
set_option maxHeartbeats 1600000 in
theorem unstableReturn_symm_apply (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (p : ℕ) (x : M) (hx : x ∈ Λ) (fixed : (T : M → M)^[p] x = x) (v : h.unstable x) :
    ((h.unstableReturn forward inverse p x hx fixed).symm v).val =
      mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T.symm : M → M)^[p]) x v.val := by
  let fp := DiffeomorphismIterates.mdifferentiable_pow T forward p
  let ip := DiffeomorphismIterates.mdifferentiable_symm_pow T inverse p
  let D := DiffeomorphismDifferential.differential (T ^ p) fp ip x
  let U := h.unstableReturn forward inverse p x hx fixed
  have action : D (U.symm v).val = v.val := by
    have actual := h.unstableReturn_apply forward inverse p x hx fixed (U.symm v)
    rw [show h.unstableReturn forward inverse p x hx fixed = U from rfl, U.apply_symm_apply] at actual
    have step := DiffeomorphismDifferential.differential_apply (T ^ p) fp ip x (U.symm v).val
    rw [DiffeomorphismIterates.coe_pow] at step
    exact step.trans actual.symm
  have inverseAction : (U.symm v).val = D.symm v.val :=
    D.injective (action.trans (D.apply_symm_apply v.val).symm)
  have actual := DiffeomorphismDifferential.differential_symm_apply (T ^ p) fp ip x v.val
  have fixedPow : (T ^ p) x = x := by simpa only [DiffeomorphismIterates.coe_pow] using fixed
  rw [fixedPow, DiffeomorphismIterates.coe_symm_pow] at actual
  exact inverseAction.trans actual

omit [FiniteDimensional ℝ E] in
set_option maxHeartbeats 1600000 in
theorem unstableReturn_inverse_norm_le (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (p : ℕ) (x : M) (hx : x ∈ Λ) (fixed : (T : M → M)^[p] x = x) :
    ‖(h.unstableReturn forward inverse p x hx fixed).symm.toContinuousLinearMap‖ ≤
      h.constant * h.contraction ^ p := by
  have fixedInverse : (T.symm : M → M)^[p] x = x := by
    have same := congrArg ((T.symm : M → M)^[p]) fixed
    have cancel := Function.LeftInverse.iterate (fun z => T.symm_apply_apply z) p x
    exact same.symm.trans cancel
  have metricTransport (y : M) (same : y = x) (w : TangentSpace (𝓘(ℝ,E)) y) :
      ‖w‖ = ‖(show TangentSpace (𝓘(ℝ,E)) x from w)‖ := by
    subst y
    rfl
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg h.constant_pos.le (pow_nonneg h.contraction_pos.le p))
  intro v
  change ‖((h.unstableReturn forward inverse p x hx fixed).symm v).val‖ ≤ _
  rw [h.unstableReturn_symm_apply]
  have bound := h.unstable_bound p x hx v.val v.property
  rw [metricTransport _ fixedInverse _] at bound
  exact bound

end HyperbolicData
end LeanShared.HyperbolicBasicSet
