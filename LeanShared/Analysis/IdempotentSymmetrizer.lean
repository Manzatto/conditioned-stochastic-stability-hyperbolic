module
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Linarith

/-! The actual symmetrizer P+P*−1 of a finite-dimensional idempotent is
invertible. The positive identity is proved, not assumed. -/
public noncomputable section
namespace LeanShared.IdempotentSymmetrizer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

@[expose] def symmetrizer (P : E →L[ℝ] E) : E →L[ℝ] E := P+star P-1

@[expose] def skew (P : E →L[ℝ] E) : E →L[ℝ] E := P-star P

theorem square (P : E →L[ℝ] E) (idem : IsIdempotentElem P) :
    symmetrizer P*symmetrizer P=1+star (skew P)*skew P := by
  have starIdem : star P*star P=star P := by
    have fact := congrArg star idem.eq
    simpa only [star_mul] using fact
  unfold symmetrizer skew
  simp only [star_sub, star_star]
  noncomm_ring [idem.eq, starIdem]

theorem selfAdjoint (P : E →L[ℝ] E) : IsSelfAdjoint (symmetrizer P) := by
  change star (P+star P-1)=P+star P-1
  simp only [star_sub, star_add, star_star, star_one]
  congr 1
  exact add_comm _ _

theorem injective (P : E →L[ℝ] E) (idem : IsIdempotentElem P) :
    Function.Injective (symmetrizer P) := by
  have zero (v : E) (hv : symmetrizer P v=0) : v=0 := by
    have equality := congrArg (fun L : E →L[ℝ] E => L v) (square P idem)
    change symmetrizer P (symmetrizer P v)=v+(skew P).adjoint (skew P v) at equality
    rw [hv, map_zero] at equality
    have innerEquality := congrArg (fun w : E => inner ℝ w v) equality
    rw [inner_zero_left, inner_add_left, ContinuousLinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at innerEquality
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg v, sq_nonneg ‖skew P v‖]
  intro u v equal
  apply sub_eq_zero.mp
  apply zero
  rw [map_sub, equal, sub_self]

theorem isUnit (P : E →L[ℝ] E) (idem : IsIdempotentElem P) : IsUnit (symmetrizer P) := by
  let e := (symmetrizer P).toLinearMap.linearEquivOfInjective (injective P idem) rfl
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact ⟨injective P idem, fun y => ⟨e.symm y,e.apply_symm_apply y⟩⟩
end LeanShared.IdempotentSymmetrizer
