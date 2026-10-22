module

public import LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.ContourProjectorContinuity

/-! Commutation and eigenvector fixation for the literal Riesz contour
projector. These identities are derived from resolvents and scalar Cauchy
integration, not assumed spectral-projector calculus. -/

public section
open Set Metric ContinuousLinearMap
open scoped Topology
namespace LeanShared.RieszContourIdempotent
open ContourProjectorContinuity

section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [CompleteSpace A] in
/-- Every resolvent commutes with the original algebra element. -/
theorem resolvent_commutes (a : A) (z : ℂ) (hz : z ∈ resolventSet ℂ a) :
    a * resolvent a z = resolvent a z * a := by
  have left : (z • (1 : A) - a) * resolvent a z = 1 := by
    simpa only [resolvent, Algebra.algebraMap_eq_smul_one] using
      Ring.mul_inverse_cancel (algebraMap ℂ A z - a) hz
  have right : resolvent a z * (z • (1 : A) - a) = 1 := by
    simpa only [resolvent, Algebra.algebraMap_eq_smul_one] using
      Ring.inverse_mul_cancel (algebraMap ℂ A z - a) hz
  have hh := left.trans right.symm
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at hh
  exact sub_right_inj.mp hh

/-- The actual contour projector commutes with its generator. -/
theorem projector_commutes (a : A) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (sphereRes : sphere c R ⊆ resolventSet ℂ a) :
    a * projector a c R = projector a c R * a := by
  have integrable : CircleIntegrable (resolvent a) c R :=
    (continuous_resolvent a _ sphereRes).circleIntegrable hR
  unfold projector contour
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  have left := map_circleIntegral (ContinuousLinearMap.mul ℂ A a) (resolvent a) c R integrable
  have right := map_circleIntegral ((ContinuousLinearMap.mul ℂ A).flip a) (resolvent a) c R integrable
  change a * (∮ z in C(c, R), resolvent a z) = ∮ z in C(c, R), a * resolvent a z at left
  change (∮ z in C(c, R), resolvent a z) * a = ∮ z in C(c, R), resolvent a z * a at right
  rw [left, right]
  exact circleIntegral.integral_congr hR (fun z hz => resolvent_commutes a z (sphereRes hz))

end Algebra

section Operators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The resolvent acts on an eigenvector by the scalar resolvent. -/
theorem resolvent_eigenvector (T : E →L[ℂ] E) (lam z : ℂ) (x : E)
    (he : T x = lam • x) (hz : z ∈ resolventSet ℂ T) (different : z ≠ lam) :
    resolvent T z x = (z - lam)⁻¹ • x := by
  have hshift : (z • (1 : E →L[ℂ] E) - T) ((z - lam)⁻¹ • x) = x := by
    rw [map_smul]
    simp only [sub_apply, smul_apply, one_apply_eq_self, he]
    rw [← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr different), one_smul]
  have hinverse : resolvent T z * (z • (1 : E →L[ℂ] E) - T) = 1 := by
    simpa only [resolvent, Algebra.algebraMap_eq_smul_one] using
      Ring.inverse_mul_cancel (algebraMap ℂ (E →L[ℂ] E) z - T) hz
  have hh := congrArg (fun Q : E →L[ℂ] E => Q ((z - lam)⁻¹ • x)) hinverse
  simpa only [mul_apply_eq_comp, hshift, one_apply_eq_self] using hh

/-- Every eigenvector with eigenvalue strictly inside the contour is fixed
by the actual Riesz contour projector. -/
theorem projector_eigenvector (T : E →L[ℂ] E) (c lam : ℂ) (R : ℝ) (hR : 0 < R)
    (sphereRes : sphere c R ⊆ resolventSet ℂ T) (inside : lam ∈ ball c R)
    (x : E) (he : T x = lam • x) : projector T c R x = x := by
  have integrable : CircleIntegrable (resolvent T) c R :=
    (continuous_resolvent T _ sphereRes).circleIntegrable hR.le
  have integral : (∮ z in C(c, R), resolvent T z x) =
      (2 * Real.pi * Complex.I : ℂ) • x := by
    calc
      (∮ z in C(c, R), resolvent T z x) = ∮ z in C(c, R), (z - lam)⁻¹ • x := by
        apply circleIntegral.integral_congr hR.le
        intro z hz
        apply resolvent_eigenvector T lam z x he (sphereRes hz)
        intro same
        subst z
        exact (ne_of_lt inside) hz
      _ = (2 * Real.pi * Complex.I : ℂ) • x := by
        rw [circleIntegral.integral_smul_const, circleIntegral.integral_sub_inv_of_mem_ball inside]
  change ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(c, R), resolvent T z) x = x
  rw [smul_apply]
  have evaluate := map_circleIntegral (ContinuousLinearMap.apply ℂ E x) (resolvent T) c R integrable
  change (∮ z in C(c, R), resolvent T z) x = ∮ z in C(c, R), resolvent T z x at evaluate
  rw [evaluate, integral, inv_smul_smul₀ Complex.two_pi_I_ne_zero]


/-- Every generalized vector belonging to an eigenvalue inside the contour is
fixed. This follows from actual contour idempotence and the eigenvector
formula, without algebraic simplicity or finite-dimensionality assumptions. -/
theorem projector_generalized (T : E →L[ℂ] E) (c lam : ℂ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R)
    (annulus : closedBall c R \ ball c r ⊆ resolventSet ℂ T)
    (inside : lam ∈ ball c r) (n : ℕ) (x : E)
    (hx : ((T - lam • 1 : E →L[ℂ] E) ^ n) x = 0) :
    projector T c r x = x := by
  let P := projector T c r
  let S := T - lam • (1 : E →L[ℂ] E)
  have sphereRes : sphere c r ⊆ resolventSet ℂ T := by
    intro z hz
    exact annulus ⟨(sphere_subset_closedBall hz).trans hrR.le,
      fun h => (ne_of_lt h) hz⟩
  have commute : P * S = S * P := by
    simp only [S, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    congr 1
    exact (projector_commutes T c r hr.le sphereRes).symm
  have hPP : P * P = P := idempotent T c r R hr hrR annulus
  induction n generalizing x with
  | zero =>
    simp only [pow_zero, one_apply_eq_self] at hx
    simp only [hx, map_zero]
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp] at hx
    have hPS : P (S x) = S x := ih (S x) hx
    let y := P x - x
    have hSy : S y = 0 := by
      have hh := congrArg (fun Q : E →L[ℂ] E => Q x) commute
      simp only [mul_apply_eq_comp] at hh
      dsimp only [y]
      rw [map_sub, ← hh, hPS, sub_self]
    have hyEigen : T y = lam • y := by
      simpa only [S, sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] using hSy
    have hPy : P y = y := projector_eigenvector T c lam r hr sphereRes inside y hyEigen
    have hPy0 : P y = 0 := by
      have hh := congrArg (fun Q : E →L[ℂ] E => Q x) hPP
      simp only [mul_apply_eq_comp] at hh
      dsimp only [y]
      rw [map_sub, hh, sub_self]
    exact sub_eq_zero.mp (hPy.symm.trans hPy0)

end Operators
end LeanShared.RieszContourIdempotent
