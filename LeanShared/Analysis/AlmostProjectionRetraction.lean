module
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FunProp

/-! A genuine continuous spectral retraction from almost self-adjoint
projections to projections. The spectral gap is derived from the actual
idempotence defect; it is not an input. -/
public noncomputable section
namespace LeanShared.AlmostProjectionRetraction
open Set

@[expose] def cutoff (x : ℝ) : ℝ := max 0 (min 1 (2*x-1/2))

theorem cutoff_continuous : Continuous cutoff := by unfold cutoff; fun_prop

theorem cutoff_zero {x : ℝ} (small : x ≤ 1/4) : cutoff x=0 := by
  unfold cutoff
  rw [max_eq_left]
  exact (min_le_right _ _).trans (by linarith)

theorem cutoff_one {x : ℝ} (large : 3/4 ≤ x) : cutoff x=1 := by
  unfold cutoff
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

private theorem defect_spectral_bound (a : A) (self : IsSelfAdjoint a)
    (small : ‖a^2-a‖ < (3/16:ℝ)) {x : ℝ} (hx : x ∈ spectrum ℝ a) :
    |x^2-x| < (3/16:ℝ) := by
  have bound := norm_apply_le_norm_cfc (fun x : ℝ => x^2-x) a hx (by fun_prop) self
  have identity : cfc (fun x : ℝ => x^2-x) a=a^2-a := by
    rw [cfc_sub (f := fun x : ℝ => x^2) (g := fun x : ℝ => x) (a := a)
      (hf := by fun_prop) (hg := by fun_prop),
      cfc_pow (fun x : ℝ => x) 2 a continuousOn_id self, cfc_id' ℝ a self]
  rw [identity, Real.norm_eq_abs] at bound
  exact bound.trans_lt small

theorem spectral_gap (a : A) (self : IsSelfAdjoint a)
    (small : ‖a^2-a‖ < (3/16:ℝ)) {x : ℝ} (hx : x ∈ spectrum ℝ a) :
    x < 1/4 ∨ 3/4 < x := by
  have estimate := defect_spectral_bound a self small hx
  have lower := (abs_lt.mp estimate).1
  by_contra! failed
  have product : 0 ≤ (x-1/4)*(3/4-x) := mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem spectral_bounded (a : A) (self : IsSelfAdjoint a)
    (small : ‖a^2-a‖ < (3/16:ℝ)) : spectrum ℝ a ⊆ Icc (-1) 2 := by
  intro x hx
  have upper := (abs_lt.mp (defect_spectral_bound a self small hx)).2
  constructor <;> nlinarith [sq_nonneg (x-1/2)]

@[expose] def retract (a : A) : A := cfc cutoff a

theorem idempotent (a : A) (self : IsSelfAdjoint a)
    (small : ‖a^2-a‖ < (3/16:ℝ)) : IsIdempotentElem (retract a) := by
  change cfc cutoff a*cfc cutoff a=cfc cutoff a
  rw [← cfc_mul cutoff cutoff a cutoff_continuous.continuousOn cutoff_continuous.continuousOn]
  apply cfc_congr
  intro x hx
  rcases spectral_gap a self small hx with low|high
  · simp only [cutoff_zero low.le, mul_zero]
  · simp only [cutoff_one high.le, mul_one]

theorem selfAdjoint (a : A) : IsSelfAdjoint (retract a) := cfc_predicate cutoff a

theorem fixes (a : A) (self : IsSelfAdjoint a) (idem : IsIdempotentElem a) : retract a=a := by
  change cfc cutoff a=a
  calc
    _ = cfc (fun x : ℝ => x) a := by
      apply cfc_congr
      intro x hx
      have member := idem.spectrum_subset ℝ hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
      rcases member with rfl|rfl <;> norm_num [cutoff]
    _ = a := cfc_id' ℝ a self

variable [ContinuousStar A]

theorem continuousOn : ContinuousOn (retract : A → A)
    {a | IsSelfAdjoint a ∧ ‖a^2-a‖ < (3/16:ℝ)} := by
  exact (continuousOn_cfc A isCompact_Icc cutoff cutoff_continuous.continuousOn).mono
    (fun a ha => ⟨ha.1,spectral_bounded a ha.1 ha.2⟩)
end LeanShared.AlmostProjectionRetraction
