module

public import LeanShared.Analysis.TransportedInverseDerivative

/-! # Inverse word derivatives on valid local chart paths

A manifold chart conjugacy is invertible only on its valid open domain.
All assumptions below are at the finitely many points of the actual word,
with inverse identities on their neighborhoods. No global Euclidean inverse
or global differentiability hypothesis is imposed.
-/

@[expose] public noncomputable section
open Filter Set
open scoped Topology
namespace LeanShared.LocalInverseWord
open CylinderPrincipalCoefficient FiniteDerivativeWord TransportedInverseDerivative

variable {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem local_inverse_fderiv_comp (F B : E → E) (x : E)
    (hF : DifferentiableAt ℝ F x) (hB : DifferentiableAt ℝ B (F x))
    (hleft : ∀ᶠ y in 𝓝 x, B (F y) = y) :
    (fderiv ℝ B (F x)).comp (fderiv ℝ F x) = ContinuousLinearMap.id ℝ E := by
  exact (hB.hasFDerivAt.comp x hF.hasFDerivAt).unique
    ((hasFDerivAt_id x).congr_of_eventuallyEq hleft)

def backwardDerivative (F B : G → E → E) {N : ℕ} (word : Fin N → G) (x : E) :
    ℕ → E →L[ℝ] E
  | 0 => ContinuousLinearMap.id ℝ E
  | k + 1 => if hk : k < N then
      (backwardDerivative F B word x k).comp
        (fderiv ℝ (B (word ⟨k, hk⟩)) (F (word ⟨k, hk⟩) (prefixOrbit F word k x)))
    else backwardDerivative F B word x k

variable (F B : G → E → E) {N : ℕ} (word : Fin N → G) (x : E)
  (hF : ∀ j : Fin N, DifferentiableAt ℝ (F (word j)) (prefixOrbit F word j.val x))
  (hB : ∀ j : Fin N, DifferentiableAt ℝ (B (word j))
    (F (word j) (prefixOrbit F word j.val x)))
  (hleft : ∀ j : Fin N, ∀ᶠ y in 𝓝 (prefixOrbit F word j.val x), B (word j) (F (word j) y) = y)

include hF in
theorem hasFDerivAt_prefixOrbit (k : ℕ) :
    HasFDerivAt (prefixOrbit F word k) (prefixDerivative F word x k) x := by
  induction k with
  | zero => exact hasFDerivAt_id x
  | succ k ih =>
      by_cases hk : k < N
      · simpa only [prefixOrbit, prefixDerivative, dite_eq_left hk, Function.comp_def] using
          (hF ⟨k, hk⟩).hasFDerivAt.comp x ih
      · simpa only [prefixOrbit, prefixDerivative, dite_eq_right hk] using ih

include hB hleft in
/-- This is the derivative of the literal reversed inverse word, evaluated
at the actual forward endpoint, with only valid local inverse assumptions. -/
theorem hasFDerivAt_inversePrefix (k : ℕ) :
    HasFDerivAt (inversePrefix B word k) (backwardDerivative F B word x k)
      (prefixOrbit F word k x) := by
  induction k with
  | zero => exact hasFDerivAt_id x
  | succ k ih =>
      by_cases hk : k < N
      · have hp : B (word ⟨k, hk⟩) (F (word ⟨k, hk⟩) (prefixOrbit F word k x)) =
            prefixOrbit F word k x := (hleft ⟨k, hk⟩).self_of_nhds
        have hi : HasFDerivAt (inversePrefix B word k) (backwardDerivative F B word x k)
            (B (word ⟨k, hk⟩) (F (word ⟨k, hk⟩) (prefixOrbit F word k x))) := by
          rw [hp]
          exact ih
        simpa only [inversePrefix, prefixOrbit, backwardDerivative, dite_eq_left hk,
          Function.comp_def] using hi.comp
            (F (word ⟨k, hk⟩) (prefixOrbit F word k x)) (hB ⟨k, hk⟩).hasFDerivAt
      · simpa only [inversePrefix, prefixOrbit, backwardDerivative, dite_eq_right hk] using ih


include hF hB hleft in
theorem backward_comp_forward (k : ℕ) :
    (backwardDerivative F B word x k).comp (prefixDerivative F word x k) =
      ContinuousLinearMap.id ℝ E := by
  induction k with
  | zero => ext v; rfl
  | succ k ih =>
      by_cases hk : k < N
      · simp only [backwardDerivative, prefixDerivative, dite_eq_left hk]
        ext v
        have he := congrArg (fun A : E →L[ℝ] E => A ((prefixDerivative F word x k) v))
          (local_inverse_fderiv_comp (F (word ⟨k, hk⟩)) (B (word ⟨k, hk⟩))
            (prefixOrbit F word k x) (hF ⟨k, hk⟩) (hB ⟨k, hk⟩) (hleft ⟨k, hk⟩))
        have hi := congrArg (fun A : E →L[ℝ] E => A v) ih
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at he hi ⊢
        rw [he]
        exact hi
      · simpa only [backwardDerivative, prefixDerivative, dite_eq_right hk] using ih

include hF hB hleft in
theorem inverse_fderiv_comp (k : ℕ) :
    (fderiv ℝ (inversePrefix B word k) (prefixOrbit F word k x)).comp
      (prefixDerivative F word x k) = ContinuousLinearMap.id ℝ E := by
  rw [(hasFDerivAt_inversePrefix F B word x hB hleft k).fderiv]
  exact backward_comp_forward F B word x hF hB hleft k

include hF hB hleft in
theorem prefixDerivative_injective (k : ℕ) :
    Function.Injective (prefixDerivative F word x k) := by
  have he := backward_comp_forward F B word x hF hB hleft k
  intro u v huv
  have hu := congrArg (fun A : E →L[ℝ] E => A u) he
  have hv := congrArg (fun A : E →L[ℝ] E => A v) he
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hu hv
  exact hu.symm.trans ((congrArg (backwardDerivative F B word x k) huv).trans hv)

end LeanShared.LocalInverseWord
