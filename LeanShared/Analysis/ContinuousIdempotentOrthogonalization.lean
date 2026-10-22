module
public import LeanShared.Analysis.IdempotentSymmetrizer
public import Mathlib.Analysis.Normed.Ring.Units

/-! The true orthogonal range projection of an actual finite-dimensional
idempotent depends continuously on that idempotent. -/
public noncomputable section
namespace LeanShared.ContinuousIdempotentOrthogonalization
open LeanShared.IdempotentSymmetrizer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

@[expose] def orthogonalize (P : E →L[ℝ] E) : E →L[ℝ] E :=
  P*Ring.inverse (symmetrizer P)

private theorem algebra (P : E →L[ℝ] E) (idem : IsIdempotentElem P) :
    IsStarProjection (orthogonalize P) ∧
      orthogonalize P*P=P ∧ P*orthogonalize P=orthogonalize P := by
  let S := symmetrizer P
  let B := Ring.inverse S
  have unit : IsUnit S := IdempotentSymmetrizer.isUnit P idem
  have left : B*S=1 := Ring.inverse_mul_cancel S unit
  have right : S*B=1 := Ring.mul_inverse_cancel S unit
  have starP : star P*star P=star P := by
    simpa only [star_mul] using congrArg star idem.eq
  have SP : S*P=star P*S := by dsimp only [S,symmetrizer]; noncomm_ring [idem.eq,starP]
  have PS : P*S=S*star P := by dsimp only [S,symmetrizer]; noncomm_ring [idem.eq,starP]
  have PP : P*S=P*star P := by dsimp only [S,symmetrizer]; noncomm_ring [idem.eq]
  have move1 : B*star P=P*B := by
    calc
      _ = (B*star P)*(S*B) := by rw [right,mul_one]
      _ = B*(star P*S)*B := by noncomm_ring
      _ = B*(S*P)*B := by rw [SP]
      _ = P*B := by rw [← mul_assoc B S P,left,one_mul]
  have move2 : B*P=star P*B := by
    calc
      _ = (B*P)*(S*B) := by rw [right,mul_one]
      _ = B*(P*S)*B := by noncomm_ring
      _ = B*(S*star P)*B := by rw [PS]
      _ = star P*B := by rw [← mul_assoc B S (star P),left,one_mul]
  have absorb : (P*B)*P=P := by
    calc
      _ = P*(B*P) := mul_assoc _ _ _
      _ = P*(star P*B) := by rw [move2]
      _ = (P*S)*B := by rw [← mul_assoc,← PP]
      _ = P := by rw [mul_assoc,right,mul_one]
  have retained : P*(P*B)=P*B := by rw [← mul_assoc,idem.eq]
  have self : IsSelfAdjoint (P*B) := by
    change star (P*B)=P*B
    have selfS : star S=S := (IdempotentSymmetrizer.selfAdjoint P).star_eq
    have selfB : star B=B := by change star (Ring.inverse S)=Ring.inverse S; rw [← Ring.inverse_star,selfS]
    rw [star_mul,selfB,move1]
  have idemR : IsIdempotentElem (P*B) := by
    change (P*B)*(P*B)=P*B
    rw [← mul_assoc,absorb]
  exact ⟨⟨idemR,self⟩,absorb,retained⟩

theorem range_eq (P : E →L[ℝ] E) (idem : IsIdempotentElem P) :
    (orthogonalize P).range=P.range := by
  ext x
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨Ring.inverse (symmetrizer P) v,rfl⟩
  · rintro ⟨v,rfl⟩
    refine ⟨P v,?_⟩
    exact congrArg (fun L : E →L[ℝ] E => L v) (algebra P idem).2.1

theorem eq_projection (P : E →L[ℝ] E) (idem : IsIdempotentElem P) :
    orthogonalize P=P.range.starProjection := by
  apply (ContinuousLinearMap.IsStarProjection.ext_iff (algebra P idem).1 isStarProjection_starProjection).mpr
  rw [range_eq P idem, Submodule.range_starProjection]

theorem continuousOn {X : Type*} [TopologicalSpace X] (K : Set X)
    (P : X → E →L[ℝ] E) (continuous : ContinuousOn P K)
    (idem : ∀ x ∈ K, IsIdempotentElem (P x)) : ContinuousOn (fun x => orthogonalize (P x)) K := by
  intro x hx
  have Scontinuous : ContinuousWithinAt (fun y => symmetrizer (P y)) K x := by
    exact ((continuous x hx).add (continuous x hx).star).sub
      (continuousWithinAt_const : ContinuousWithinAt (fun _ : X => (1 : E →L[ℝ] E)) K x)
  obtain ⟨u,hu⟩ := IdempotentSymmetrizer.isUnit (P x) (idem x hx)
  have inverseAt : ContinuousAt (Ring.inverse : (E →L[ℝ] E) → E →L[ℝ] E) (symmetrizer (P x)) := by
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  change ContinuousWithinAt (fun y => P y*Ring.inverse (symmetrizer (P y))) K x
  exact (continuous x hx).mul (inverseAt.comp_continuousWithinAt (f := fun y : X => symmetrizer (P y)) Scontinuous)
end LeanShared.ContinuousIdempotentOrthogonalization
