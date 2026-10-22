module
public import LeanShared.Dynamics.HyperbolicLinearRechart
public import LeanShared.Dynamics.HyperbolicThermodynamics
public import LeanShared.Dynamics.PressureRestriction

/-! The actual unstable Jacobian and thermodynamic potential are unchanged
by the isometric transport of the supplied tangent metric. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Topology
namespace LeanShared.HyperbolicLinearRechart
open HyperbolicBasicSet LinearRechartedManifold ThermodynamicDefinitions

/-- Isometric changes of the ambient source and target preserve the
intrinsic Jacobian of a restriction to any actual subspace. -/
theorem normDet_domRestrict_isometric_conjugacy
    {A B C D : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [NormedAddCommGroup C] [InnerProductSpace ℝ C] [FiniteDimensional ℝ C]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    (j : A ≃ₗᵢ[ℝ] C) (k : B ≃ₗᵢ[ℝ] D)
    (f : A →ₗ[ℝ] B) (g : C →ₗ[ℝ] D)
    (commutes : ∀ v, g (j v) = k (f v)) (U : Submodule ℝ A) :
    (g.domRestrict (U.map j.toLinearEquiv.toLinearMap)).normDet =
      (f.domRestrict U).normDet := by
  let u : U ≃ₗᵢ[ℝ] U.map j.toLinearEquiv.toLinearMap := j.submoduleMap U
  have equal : (g.domRestrict (U.map j.toLinearEquiv.toLinearMap)).comp
      u.toLinearEquiv.toLinearMap =
      k.toLinearEquiv.toLinearMap.comp (f.domRestrict U) := by
    ext v
    exact commutes v.val
  have determinant := congrArg LinearMap.normDet equal
  have left := LinearMap.normDet_comp_of_finrank_eq u.toLinearEquiv.toLinearMap
    (g.domRestrict (U.map j.toLinearEquiv.toLinearMap)) u.toLinearEquiv.finrank_eq
  have right := LinearMap.normDet_comp (f.domRestrict U) k.toLinearEquiv.toLinearMap
  have both := left.symm.trans (determinant.trans right)
  have unit : u.toLinearEquiv.toLinearMap.normDet = 1 :=
    u.toLinearIsometry.normDet_eq_one
  rw [unit, mul_one] at both
  have restricted : (k.toLinearEquiv.toLinearMap.domRestrict
      (f.domRestrict U).range).normDet = 1 :=
    (k.toLinearIsometry.comp (f.domRestrict U).range.subtypeₗᵢ).normDet_eq_one
  simpa only [restricted, one_mul] using both

variable {E F M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  (e : E ≃L[ℝ] F) {T : M ≃ₜ M} {Λ : Set M}

theorem unstableJacobian_domRestrict (h : HyperbolicData (E := E) T Λ) (x : M) :
    h.unstableJacobian x = ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T x).toLinearMap.domRestrict
      (h.unstable x)).normDet := by
  exact LinearMap.normDet_codRestrict _

theorem unstableJacobian_eq (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) (x : M) :
    let oldJacobian := h.unstableJacobian x;
    let transported := transport e h forward inverse;
    let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x);
    letI := charts (M := M) e;
    letI := manifold (M := M) e;
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
      ⟨transportMetric e original⟩;
    transported.unstableJacobian x = oldJacobian := by
  let oldJacobian := h.unstableJacobian x
  let oldUnstable := h.unstable x
  let oldDerivative := mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T x
  let transported := transport e h forward inverse
  have unstable := transport_unstable e h forward inverse
  let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x)
  let := charts (M := M) e
  let := manifold (M := M) e
  let : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
    ⟨transportMetric e original⟩
  let j := identityIsometry (M := M) e original x
  let k := identityIsometry (M := M) e original (T x)
  have commutes (v : TangentSpace (𝓘(ℝ,E)) x) :
      mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) T x (j v) = k (oldDerivative v) := by
    exact congrArg (fun l => l v) (mfderiv_rechart_comp e forward x)
  have determinant := normDet_domRestrict_isometric_conjugacy j k
    oldDerivative.toLinearMap (mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) T x).toLinearMap
    commutes oldUnstable
  change transported.unstableJacobian x = oldJacobian
  change transported.unstableJacobian x = h.unstableJacobian x
  rw [unstableJacobian_domRestrict, unstableJacobian_domRestrict]
  change ((mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) T x).toLinearMap.domRestrict
    (transported.unstable x)).normDet =
      (oldDerivative.toLinearMap.domRestrict oldUnstable).normDet
  rw [congrFun unstable x]
  exact determinant

theorem potential_eq (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) (g : M → ℝ) :
    let oldPotential := h.potential g;
    let transported := transport e h forward inverse;
    let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x);
    letI := charts (M := M) e;
    letI := manifold (M := M) e;
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
      ⟨transportMetric e original⟩;
    transported.potential g = oldPotential := by
  funext x
  exact congrArg (fun J => Real.log (g x) - Real.log J)
    (unstableJacobian_eq e h forward inverse x)


/-- The transported basic set has exactly the original physical potential
at every point, including points outside the invariant core. -/
theorem basic_potential_eq {V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) (g : M → ℝ) :
    let oldPotential := b.hyperbolic.potential g;
    let transported := transportBasic e b forward inverse;
    let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x);
    letI := charts (M := M) e;
    letI := manifold (M := M) e;
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
      ⟨transportMetric e original⟩;
    transported.hyperbolic.potential g = oldPotential := by
  cases b with
  | mk h _ _ _ _ _ => exact potential_eq e h forward inverse g

end LeanShared.HyperbolicLinearRechart
