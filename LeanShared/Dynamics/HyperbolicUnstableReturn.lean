module

public import LeanShared.Dynamics.HyperbolicUnstableJacobianCocycle
public import LeanShared.Geometry.FlatTangentIsometry

/-! At a genuine periodic point, the actual unstable differential returns
to the SAME native Riemannian fiber. Its norm determinant is exactly the
literal Jacobian product, without any coordinate-frame volume factor. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}
namespace HyperbolicData

@[expose] def unstableTransport (h : HyperbolicData (E := E) T Λ) (x y : M) (same : x = y) :
    h.unstable x ≃ₗᵢ[ℝ] h.unstable y := by
  subst y
  exact LinearIsometryEquiv.refl ℝ _

omit [FiniteDimensional ℝ E] in
theorem unstableTransport_apply (h : HyperbolicData (E := E) T Λ) (x y : M) (same : x = y)
    (v : h.unstable x) : (unstableTransport h x y same v).val = v.val := by
  subst y
  rfl

@[expose] def unstableReturn (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (p : ℕ) (x : M) (hx : x ∈ Λ) (fixed : (T : M → M)^[p] x = x) :
    h.unstable x ≃L[ℝ] h.unstable x :=
  (h.unstableCocycle forward inverse x hx p).trans
    (unstableTransport h _ _ ((cocyclePoint_eq_iterate T x p).trans fixed)).toContinuousLinearEquiv

omit [FiniteDimensional ℝ E] in
theorem unstableReturn_apply (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (p : ℕ) (x : M) (hx : x ∈ Λ) (fixed : (T : M → M)^[p] x = x) (v : h.unstable x) :
    (h.unstableReturn forward inverse p x hx fixed v).val =
      mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[p]) x v.val := by
  exact (unstableTransport_apply h (cocyclePoint T x p) x
    ((cocyclePoint_eq_iterate T x p).trans fixed)
    (h.unstableCocycle forward inverse x hx p v)).trans
    (h.unstableCocycle_apply forward inverse x hx p v)

theorem unstableReturn_normDet (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (p : ℕ) (x : M) (hx : x ∈ Λ) (fixed : (T : M → M)^[p] x = x) :
    (h.unstableReturn forward inverse p x hx fixed).toLinearMap.normDet =
      ∏ j ∈ Finset.range p, h.unstableJacobian ((T : M → M)^[j] x) := by
  have preserves := NormDetIsometry.comp (h.unstableCocycle forward inverse x hx p).toLinearMap
    (unstableTransport h _ _ ((cocyclePoint_eq_iterate T x p).trans fixed)).toLinearIsometry
  exact preserves.trans (h.unstableCocycle_normDet forward inverse x hx p)

end HyperbolicData
end LeanShared.HyperbolicBasicSet
