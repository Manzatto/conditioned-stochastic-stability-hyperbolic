module

public import LeanShared.Dynamics.HyperbolicStableUniqueness
public import LeanShared.Dynamics.HyperbolicUnstableUniqueness
public import LeanShared.Dynamics.HyperbolicThermodynamics

/-! The actual continuous hyperbolic projection, unstable Jacobian and
thermodynamic potential are independent of the chosen hyperbolic certificate
for a fixed diffeomorphism and core. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
namespace LeanShared.HyperbolicBasicSet
private theorem restricted_volume_congr {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (D : U →L[ℝ] V) (P Q : Submodule ℝ U) (same : P=Q) :
    (D.toLinearMap.comp P.subtype).normDet=(D.toLinearMap.comp Q.subtype).normDet := by
  subst Q
  rfl

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (TangentSpace (𝓘(ℝ,E)) : M → Type _)]
  {T : M ≃ₜ M} {Λ : Set M}

theorem HyperbolicData.projection_eq (h k : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) (x : M) (hx : x ∈ Λ) :
    h.projection x=k.projection x := by
  apply ContinuousLinearMap.ext
  intro v
  have idemH (w : TangentSpace (𝓘(ℝ,E)) x) : h.projection x (h.projection x w)=h.projection x w :=
    congrArg (fun A : TangentSpace (𝓘(ℝ,E)) x →L[ℝ] TangentSpace (𝓘(ℝ,E)) x => A w) (h.projection_idempotent x hx)
  have idemK (w : TangentSpace (𝓘(ℝ,E)) x) : k.projection x (k.projection x w)=k.projection x w :=
    congrArg (fun A : TangentSpace (𝓘(ℝ,E)) x →L[ℝ] TangentSpace (𝓘(ℝ,E)) x => A w) (k.projection_idempotent x hx)
  have stable : h.projection x v ∈ k.stable x := by
    rw [←h.stable_eq k forward inverse x hx,←h.projection_range x hx]
    exact LinearMap.mem_range.mpr ⟨v,rfl⟩
  have fixed : k.projection x (h.projection x v)=h.projection x v := by
    rw [←k.projection_range x hx] at stable
    obtain ⟨w,hw⟩ := stable
    rw [←hw]
    exact idemK w
  have unstable : v-h.projection x v ∈ k.unstable x := by
    rw [←h.unstable_eq k forward inverse x hx,←h.projection_kernel x hx]
    change h.projection x (v-h.projection x v)=0
    rw [map_sub,idemH,sub_self]
  rw [←k.projection_kernel x hx] at unstable
  change k.projection x (v-h.projection x v)=0 at unstable
  rw [map_sub,fixed] at unstable
  exact (sub_eq_zero.mp unstable).symm

theorem HyperbolicData.unstableJacobian_eq (h k : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) (x : M) (hx : x ∈ Λ) :
    h.unstableJacobian x=k.unstableJacobian x := by
  have forget (a : HyperbolicData (E := E) T Λ) : a.unstableJacobian x=
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T x).toLinearMap.comp (a.unstable x).subtype).normDet := by
    unfold HyperbolicData.unstableJacobian
    exact LinearMap.normDet_codRestrict _
  exact (forget h).trans ((restricted_volume_congr _ _ _ (h.unstable_eq k forward inverse x hx)).trans (forget k).symm)

theorem HyperbolicData.potential_eqOn (h k : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) (g : M → ℝ) :
    EqOn (h.potential g) (k.potential g) Λ := by
  intro x hx
  dsimp [HyperbolicData.potential]
  rw [h.unstableJacobian_eq k forward inverse x hx]

end LeanShared.HyperbolicBasicSet
