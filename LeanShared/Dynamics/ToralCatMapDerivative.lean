module

public import LeanShared.Dynamics.ToralCatMapQuotientDifferential
public import LeanShared.Dynamics.ToralCatMapHyperbolicLift
public import LeanShared.Geometry.DiffeomorphismIterates

/-! The literal manifold derivative of the concrete toral cat map and
its inverse is conjugate to the explicit real linear lift through the
actual quotient differential. -/

set_option maxHeartbeats 800000
@[expose] public noncomputable section
open Set IsManifold Bundle Function
open scoped Manifold ContDiff Bundle Topology
namespace LeanShared.ToralCatMap

def realTangentFrame (x : Torus) : (ℝ × ℝ) ≃L[ℝ] TangentSpace (𝓘(ℝ, HilbertModel)) x :=
  liftHilbertEquivalence.trans (tangentFrame x)

theorem realTangentFrame_quotient (z v : ℝ × ℝ) :
    realTangentFrame (quotient z) v =
      mfderiv (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, HilbertModel)) quotient z
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v) :=
  (quotientDifferential z v).symm

set_option backward.isDefEq.respectTransparency false in
private theorem derivative_from_quotient (f : Torus → Torus) (F : (ℝ × ℝ) → (ℝ × ℝ))
    (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (smooth : MDifferentiable (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) f)
    (liftSmooth : MDifferentiable (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ × ℝ)) F)
    (derivative : ∀ z, fderiv ℝ F z = A)
    (commute : f ∘ quotient = quotient ∘ F) (z v : ℝ × ℝ) :
    mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) f (quotient z)
      (realTangentFrame (quotient z) v) = realTangentFrame (f (quotient z)) (A v) := by
  have quotDiff : MDifferentiable (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, HilbertModel)) quotient :=
    smooth_quotient.mdifferentiable (by simp)
  have same := mfderiv_congr (I := 𝓘(ℝ, ℝ × ℝ)) (I' := 𝓘(ℝ, HilbertModel)) (x := z) commute
  rw [mfderiv_comp z (smooth _) (quotDiff _), mfderiv_comp z (quotDiff _) (liftSmooth _)] at same
  have eval := congrArg (fun D => D ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v)) same
  change mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) f (quotient z)
      (mfderiv (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, HilbertModel)) quotient z
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v)) =
    mfderiv (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, HilbertModel)) quotient (F z)
      (mfderiv (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ × ℝ)) F z
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm v)) at eval
  rw [mfderiv_eq_fderiv, derivative] at eval
  have point : f (quotient z) = quotient (F z) := congrFun commute z
  rw [point, realTangentFrame_quotient]
  rw [realTangentFrame_quotient]
  exact eval

theorem quotient_surjective : Surjective quotient := by
  intro x
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective x.1
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk_surjective x.2
  exact ⟨(a,b), Prod.ext ha hb⟩

theorem quotient_inverse (z : ℝ × ℝ) : quotient (inverse z) = inverse (quotient z) := by
  ext <;> simp only [quotient, inverse, AddCircle.coe_add, AddCircle.coe_sub]

theorem derivative_map_realFrame (x : Torus) (v : ℝ × ℝ) :
    mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) (map (G := UnitAddCircle)) x
      (realTangentFrame x v) = realTangentFrame (map x) (map v) := by
  obtain ⟨z, rfl⟩ := quotient_surjective x
  exact derivative_from_quotient map map linear.toContinuousLinearMap
    (smooth_map.mdifferentiable (by simp)) (contDiff_map.contMDiff.mdifferentiable (by simp))
    fderiv_map (funext (fun z => (quotient_map z).symm)) z v

theorem derivative_inverse_realFrame (x : Torus) (v : ℝ × ℝ) :
    mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) (inverse (G := UnitAddCircle)) x
      (realTangentFrame x v) = realTangentFrame (inverse x) (inverse v) := by
  obtain ⟨z, rfl⟩ := quotient_surjective x
  exact derivative_from_quotient inverse inverse inverseLinear.toContinuousLinearMap
    (smooth_inverse.mdifferentiable (by simp)) (contDiff_inverse.contMDiff.mdifferentiable (by simp))
    fderiv_inverse (funext (fun z => (quotient_inverse z).symm)) z v

set_option backward.isDefEq.respectTransparency false in
private theorem derivative_iterate_from_frame (f : Torus → Torus) (F : (ℝ × ℝ) → (ℝ × ℝ))
    (smooth : MDifferentiable (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) f)
    (one : ∀ x v, mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) f x
      (realTangentFrame x v) = realTangentFrame (f x) (F v))
    (n : ℕ) (x : Torus) (v : ℝ × ℝ) :
    mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) (f^[n]) x
      (realTangentFrame x v) = realTangentFrame (f^[n] x) (F^[n] v) := by
  induction n with
  | zero => simp only [Function.iterate_zero, mfderiv_id, ContinuousLinearMap.id_apply, id_eq]
  | succ n ih =>
    have iterated := DiffeomorphismIterates.mdifferentiable_iterate f smooth n
    rw [Function.iterate_succ', mfderiv_comp x (smooth _) (iterated _)]
    change mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) f (f^[n] x)
      (mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) (f^[n]) x
        (realTangentFrame x v)) = _
    rw [ih, one, Function.iterate_succ_apply']
    rfl

theorem derivative_iterate_realFrame (n : ℕ) (x : Torus) (v : ℝ × ℝ) :
    mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) ((homeomorph : Torus → Torus)^[n]) x
      (realTangentFrame x v) = realTangentFrame (homeomorph^[n] x) ((map (G := ℝ))^[n] v) :=
  derivative_iterate_from_frame homeomorph map (smooth_homeomorph.mdifferentiable (by simp))
    derivative_map_realFrame n x v

theorem derivative_inverse_iterate_realFrame (n : ℕ) (x : Torus) (v : ℝ × ℝ) :
    mfderiv (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) ((homeomorph.symm : Torus → Torus)^[n]) x
      (realTangentFrame x v) = realTangentFrame (homeomorph.symm^[n] x) ((inverse (G := ℝ))^[n] v) :=
  derivative_iterate_from_frame homeomorph.symm inverse (smooth_homeomorph_symm.mdifferentiable (by simp))
    derivative_inverse_realFrame n x v

end LeanShared.ToralCatMap
