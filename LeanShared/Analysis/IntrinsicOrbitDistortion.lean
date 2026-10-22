module

public import LeanShared.Analysis.IntrinsicDistortionRatio
public import LeanShared.Analysis.ActualWordWeightProduct
public import LeanShared.Analysis.OrbitWeightDistortion

/-! Literal deterministic orbit/Jacobian distortion gives the mixed ratio
bound used by nearby-word principal coefficients. The original cutoff may
vanish; its positive envelope is used only in the denominator. Orbital
errors may be actual chart or Riemannian distances, without silently
identifying an arbitrary ambient metric with the Riemannian distance. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace LeanShared.IntrinsicOrbitDistortion
open CylinderPrincipalCoefficient IntrinsicPrincipalDensity
variable {G X : Type*} [TopologicalSpace G] [TopologicalSpace X]
  (F : G → X → X) (E : X → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)]
  (D : ∀ a x, E x ≃L[ℝ] E (F a x))
  (unstable : ∀ x, Submodule ℝ (E x))

private theorem le_exp_mul_of_log (a b C : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : |Real.log a - Real.log b| ≤ C) : a ≤ Real.exp C * b := by
  have hl : Real.log a ≤ C + Real.log b := by
    have := (le_abs_self (Real.log a - Real.log b)).trans h
    linarith
  simpa only [Real.exp_add, Real.exp_log ha, Real.exp_log hb] using Real.exp_le_exp.mpr hl

/-- Precise ordinary sources are a summable actual orbital error, a
pointwise Hölder weight increment, and logarithmic distortion of the
actual transported unstable volume Jacobian. Their scalar ratio consequence
is proved here; it is not an independent random principal-bound input. -/
theorem ratio_bound (g : X → ℝ) (hg : ∀ x, 0 ≤ g x)
    {N : ℕ} (word : Fin N → G) (x y z : X) (e : Fin N → ℝ)
    (H B BJ ε : ℝ) (hH : 0 ≤ H) (hε : 0 < ε)
    (hdiff : ∀ j : Fin N,
      |g (prefixOrbit F word j.val x) - g (prefixOrbit F word j.val z)| ≤ H * e j)
    (hsum : (∑ j, e j) ≤ B)
    (hjac : |Real.log (unstableJacobian F E D (List.ofFn word) z (unstable z)) -
      Real.log (unstableJacobian F E D (List.ofFn word) y (unstable y))| ≤ BJ) :
    IntrinsicDistortionRatio.ratio F E D unstable g (fun q => g q + ε) N (word, (x, y, z)) ≤
      Real.exp ((H / ε) * B + BJ) := by
  let w := List.ofFn word
  let envelope := fun q => g q + ε
  have hepos : ∀ q, 0 < envelope q := fun q => add_pos_of_nonneg_of_pos (hg q) hε
  have he0 : ∀ q, 0 ≤ envelope q := fun q => (hepos q).le
  have hweight : weight F g w x ≤ weight F envelope w x := by
    rw [ActualWordWeightProduct.intrinsic_weight_eq_product,
      ActualWordWeightProduct.intrinsic_weight_eq_product]
    exact Finset.prod_le_prod₀ (fun j _ => hg _) (fun j _ => le_add_of_nonneg_right hε.le)
  have henv := OrbitWeightDistortion.positive_envelope_wordWeight_le F g word x z e H B ε
    hH hε (fun j => ⟨hg _, hg _⟩) hdiff hsum
  have henv' : weight F envelope w x ≤ Real.exp ((H / ε) * B) * weight F envelope w z := by
    dsimp only [w]
    rw [ActualWordWeightProduct.intrinsic_weight_eq_cylinder F envelope he0 word x,
      ActualWordWeightProduct.intrinsic_weight_eq_cylinder F envelope he0 word z]
    exact henv
  have hraw : weight F g w x ≤ Real.exp ((H / ε) * B) * weight F envelope w z :=
    hweight.trans henv'
  have hy : 0 < unstableJacobian F E D w y (unstable y) := unstableJacobian_pos F E D _ _ _
  have hz : 0 < unstableJacobian F E D w z (unstable z) := unstableJacobian_pos F E D _ _ _
  have hwz : 0 < weight F envelope w z := IntrinsicDistortionRatio.weight_positive F envelope hepos _ _
  have hj : unstableJacobian F E D w z (unstable z) ≤
      Real.exp BJ * unstableJacobian F E D w y (unstable y) :=
    le_exp_mul_of_log _ _ BJ hz hy hjac
  have hnum := mul_le_mul hraw hj hz.le (mul_nonneg (Real.exp_pos _).le hwz.le)
  change weight F g w x * unstableJacobian F E D w z (unstable z) /
    (unstableJacobian F E D w y (unstable y) * weight F envelope w z) ≤ _
  apply (div_le_iff₀ (mul_pos hy hwz)).mpr
  exact hnum.trans_eq (by rw [Real.exp_add]; ring)

end LeanShared.IntrinsicOrbitDistortion
