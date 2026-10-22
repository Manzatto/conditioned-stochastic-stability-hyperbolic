module

public import LeanShared.Analysis.WordHyperbolicityFactors

/-! # Principal density on point-dependent Hilbert tangent fibers

The fibers may be the actual Riemannian tangent spaces; no global coordinate
frame is used. One-step derivative equivalences construct the derivative of
each chronological word. Its stable preimage, transported unstable fiber,
volume Jacobian and inverse unstable norm define the intrinsic scalar used
by the manifold pressure-block argument.
-/

@[expose] public noncomputable section
open Set
namespace LeanShared.IntrinsicPrincipalDensity

variable {G M : Type*} (F : G → M → M)

def orbit : List G → M → M
  | [], x => x
  | a :: word, x => orbit word (F a x)

variable (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)]
  (D : ∀ a x, E x ≃L[ℝ] E (F a x))

/-- Literal chain-rule product between the initial and endpoint fibers. -/
def derivative : (word : List G) → (x : M) → E x ≃L[ℝ] E (orbit F word x)
  | [], x => ContinuousLinearEquiv.refl ℝ (E x)
  | a :: word, x => (D a x).trans (derivative word (F a x))

def unstableImage (word : List G) (x : M) (U : Submodule ℝ (E x)) :
    Submodule ℝ (E (orbit F word x)) := U.map (derivative F E D word x).toLinearMap

def stablePreimage (word : List G) (x : M) (S : Submodule ℝ (E (orbit F word x))) :
    Submodule ℝ (E x) := S.comap (derivative F E D word x).toLinearMap

def stableFactor (word : List G) (x : M) (S : Submodule ℝ (E (orbit F word x))) : ℝ :=
  ‖((derivative F E D word x) : E x →L[ℝ] E (orbit F word x)).restrict
    (show MapsTo (derivative F E D word x) (stablePreimage F E D word x S) S from fun _ hv => hv)‖

def inverseFactor (word : List G) (x : M) (U : Submodule ℝ (E x)) : ℝ :=
  ‖((derivative F E D word x).symm : E (orbit F word x) →L[ℝ] E x).domRestrict
    (unstableImage F E D word x U)‖

def unstableJacobian (word : List G) (x : M) (U : Submodule ℝ (E x)) : ℝ :=
  (((derivative F E D word x) : E x →L[ℝ] E (orbit F word x)).restrict
    (show MapsTo (derivative F E D word x) U (unstableImage F E D word x U) from
      fun v hv => Submodule.mem_map.mpr ⟨v, hv, rfl⟩)).toLinearMap.normDet

/-- The transported Jacobian is positive since the actual derivative is
injective, including when the unstable dimension is zero. -/
theorem unstableJacobian_pos (word : List G) (x : M) (U : Submodule ℝ (E x)) :
    0 < unstableJacobian F E D word x U := by
  let A := ((derivative F E D word x) : E x →L[ℝ] E (orbit F word x)).restrict
    (show MapsTo (derivative F E D word x) U (unstableImage F E D word x U) from
      fun v hv => Submodule.mem_map.mpr ⟨v, hv, rfl⟩)
  have hA : Function.Injective A.toLinearMap := by
    intro u v huv
    apply Subtype.ext
    exact (derivative F E D word x).injective (congrArg Subtype.val huv)
  have hne := (A.toLinearMap.normDet_ne_zero_tfae.out 5 1).mp hA
  exact lt_of_le_of_ne (LinearMap.normDet_nonneg _) (Ne.symm hne)

omit [∀ x, FiniteDimensional ℝ (E x)] in
/-- The backward factor controls minimal expansion on the actual unstable
fiber, using the inverse of the constructed derivative word. -/
theorem norm_le_inverseFactor_mul (word : List G) (x : M) (U : Submodule ℝ (E x))
    (v : E x) (hv : v ∈ U) :
    ‖v‖ ≤ inverseFactor F E D word x U * ‖derivative F E D word x v‖ := by
  have hm : derivative F E D word x v ∈ unstableImage F E D word x U :=
    Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  have hb := (((derivative F E D word x).symm : E (orbit F word x) →L[ℝ] E x).domRestrict
    (unstableImage F E D word x U)).le_opNorm ⟨derivative F E D word x v, hm⟩
  change ‖(derivative F E D word x).symm (derivative F E D word x v)‖ ≤
    inverseFactor F E D word x U * ‖derivative F E D word x v‖ at hb
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hb

omit [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)] in
def weight (g : M → ℝ) : List G → M → ℝ
  | [], _ => 1
  | a :: word, x => g x * weight g word (F a x)

omit [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)] in
theorem weight_nonneg (g : M → ℝ) (hg : ∀ x, 0 ≤ g x) (word : List G) (x : M) :
    0 ≤ weight F g word x := by
  induction word generalizing x with
  | nil => exact zero_le_one
  | cons a word ih => exact mul_nonneg (hg x) (ih (F a x))


def density (g : M → ℝ) (stable unstable : (x : M) → Submodule ℝ (E x))
    (N : ℕ) (t s : ℝ) : (Fin N → G) × M → ℝ := fun z =>
  CylinderPrincipalCoefficient.principalDensity
    (fun p => weight F g (List.ofFn p.1) p.2)
    (fun p => unstableJacobian F E D (List.ofFn p.1) p.2 (unstable p.2))
    (fun p => stableFactor F E D (List.ofFn p.1) p.2
      (stable (orbit F (List.ofFn p.1) p.2)))
    (fun p => inverseFactor F E D (List.ofFn p.1) p.2 (unstable p.2)) t s z

theorem density_nonneg (g : M → ℝ) (hg : ∀ x, 0 ≤ g x)
    (stable unstable : (x : M) → Submodule ℝ (E x)) (N : ℕ) (t s : ℝ)
    (z : (Fin N → G) × M) : 0 ≤ density F E D g stable unstable N t s z := by
  apply mul_nonneg
  · exact div_nonneg (weight_nonneg F g hg _ _) (unstableJacobian_pos F E D _ _ _).le
  · change 0 ≤ max (stableFactor F E D (List.ofFn z.1) z.2
      (stable (orbit F (List.ofFn z.1) z.2)) ^ t) _
    have hs : 0 ≤ stableFactor F E D (List.ofFn z.1) z.2
        (stable (orbit F (List.ofFn z.1) z.2)) := by
      exact norm_nonneg
        (((derivative F E D (List.ofFn z.1) z.2) : E z.2 →L[ℝ] E (orbit F (List.ofFn z.1) z.2)).restrict
          (show MapsTo (derivative F E D (List.ofFn z.1) z.2)
            (stablePreimage F E D (List.ofFn z.1) z.2 (stable (orbit F (List.ofFn z.1) z.2)))
            (stable (orbit F (List.ofFn z.1) z.2)) from fun _ hv => hv))
    exact le_max_of_le_left (Real.rpow_nonneg hs t)


end LeanShared.IntrinsicPrincipalDensity
