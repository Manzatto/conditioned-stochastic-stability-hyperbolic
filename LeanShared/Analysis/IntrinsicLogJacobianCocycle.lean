module
public import LeanShared.Analysis.IntrinsicJacobianCocycle
public import LeanShared.Dynamics.ThermodynamicDefinitions

/-! Actual logarithmic weight/Jacobian potential along invariant tangent
fibers. This is the finite-word algebra needed by the cited BT pressure
formula; no pressure inequality or off-core extension conclusion is assumed. -/
@[expose] public noncomputable section
open Set
namespace LeanShared.IntrinsicPrincipalDensity
variable {G M : Type*} (F : G → M → M)

theorem weight_pos (g : M → ℝ) (K : Set M) (hK : ∀ a, MapsTo (F a) K K)
    (hg : ∀ x ∈ K, 0 < g x) (word : List G) (x : M) (hx : x ∈ K) :
    0 < weight F g word x := by
  induction word generalizing x with
  | nil => exact zero_lt_one
  | cons a word ih => exact mul_pos (hg x hx) (ih (F a x) (hK a hx))

variable (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)]
  (D : ∀ a x, E x ≃L[ℝ] E (F a x))

theorem unstableJacobian_nil (x : M) (U : Submodule ℝ (E x)) :
    unstableJacobian F E D [] x U = 1 := by
  rw [unstableJacobian_eq_domRestrict]
  exact U.subtypeₗᵢ.normDet_eq_one

theorem oneStepJacobian_pos (a : G) (x : M) (U : Submodule ℝ (E x)) :
    0 < ((D a x).toLinearMap.domRestrict U).normDet := by
  have hinj : Function.Injective ((D a x).toLinearMap.domRestrict U) := by
    intro u v huv
    exact Subtype.ext ((D a x).injective huv)
  have hne := (((D a x).toLinearMap.domRestrict U).normDet_ne_zero_tfae.out 5 1).mp hinj
  exact lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm hne)

def logPotentialSum (g : M → ℝ) (U : (x : M) → Submodule ℝ (E x)) : List G → M → ℝ
  | [], _ => 0
  | a :: word, x => Real.log (g x) - Real.log (((D a x).toLinearMap.domRestrict (U x)).normDet) +
      logPotentialSum g U word (F a x)

theorem log_weight_div_jacobian (g : M → ℝ) (K : Set M)
    (hK : ∀ a, MapsTo (F a) K K) (hg : ∀ x ∈ K, 0 < g x)
    (U : (x : M) → Submodule ℝ (E x))
    (hinv : ∀ a x, x ∈ K → (U x).map (D a x).toLinearMap = U (F a x))
    (word : List G) (x : M) (hx : x ∈ K) :
    Real.log (weight F g word x / unstableJacobian F E D word x (U x)) =
      logPotentialSum F E D g U word x := by
  induction word generalizing x with
  | nil => simp only [weight, unstableJacobian_nil, div_self one_ne_zero, Real.log_one, logPotentialSum]
  | cons a word ih =>
    rw [weight, unstableJacobian_cons_of_invariant F E D K U hinv a word x hx,
      Real.log_div (mul_pos (hg x hx) (weight_pos F g K hK hg word (F a x) (hK a hx))).ne'
        (mul_pos (oneStepJacobian_pos F E D a x (U x))
          (unstableJacobian_pos F E D word (F a x) (U (F a x)))).ne',
      Real.log_mul (hg x hx).ne' (weight_pos F g K hK hg word (F a x) (hK a hx)).ne',
      Real.log_mul (oneStepJacobian_pos F E D a x (U x)).ne'
        (unstableJacobian_pos F E D word (F a x) (U (F a x))).ne']
    have htail := ih (F a x) (hK a hx)
    rw [Real.log_div (weight_pos F g K hK hg word (F a x) (hK a hx)).ne'
      (unstableJacobian_pos F E D word (F a x) (U (F a x))).ne'] at htail
    change _ = Real.log (g x) - Real.log (((D a x).toLinearMap.domRestrict (U x)).normDet) + _
    linarith

/-- A constant chronological word gives the genuine Bowen orbit sum. -/
theorem logPotentialSum_replicate (g : M → ℝ)
    (U : (x : M) → Submodule ℝ (E x)) (a : G) (N : ℕ) (x : M) :
    logPotentialSum F E D g U (List.replicate N a) x =
      ThermodynamicDefinitions.orbitSum (F a)
        (fun y => Real.log (g y) - Real.log (((D a y).toLinearMap.domRestrict (U y)).normDet)) N x := by
  induction N generalizing x with
  | zero => simp [logPotentialSum, ThermodynamicDefinitions.orbitSum]
  | succ N ih =>
    rw [List.replicate_succ, logPotentialSum, ih]
    unfold ThermodynamicDefinitions.orbitSum
    rw [Finset.sum_range_succ']
    simp only [Function.iterate_zero_apply, Function.iterate_succ_apply]
    exact add_comm (Real.log (g x) - Real.log (((D a x).toLinearMap.domRestrict (U x)).normDet)) _

end LeanShared.IntrinsicPrincipalDensity
