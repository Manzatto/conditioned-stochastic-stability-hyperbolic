module

public import LeanShared.Analysis.IntrinsicPrincipalDensity
public import LeanShared.Analysis.ActualWordMicrolocalBound

/-!
# Local continuity of the literal intrinsic principal density

The four scalar continuity inputs are ordinary tangent-chart facts:
accumulated weight, volume Jacobian, stable restricted derivative norm and
inverse unstable norm. Their fibers are point-dependent. The actual word
Jacobian is proved positive, so division and nonnegative real powers yield
continuity on each valid cylinder, including zero-dimensional bundles.
No global frame or continuity of the final pressure coefficient is assumed.
-/

@[expose] public noncomputable section

namespace LeanShared.ContinuousIntrinsicPrincipalDensity

open Set IntrinsicPrincipalDensity

variable {G M : Type*} (F : G → M → M)
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)]
  (D : ∀ a x, E x ≃L[ℝ] E (F a x))

omit [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)] in
/-- The intrinsic chronological orbit is the actual transfer-word orbit. -/
theorem orbit_eq (word : List G) (x : M) :
    IntrinsicPrincipalDensity.orbit F word x = ActualFiniteRegularWord.orbit F word x := by
  induction word generalizing x with
  | nil => rfl
  | cons a word ih => exact ih (F a x)

omit [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)] in
/-- The weight in the geometric density is exactly the real accumulated
transfer weight; one applies this also to the positive envelope. -/
theorem weight_eq (g : M → ℝ) (word : List G) (x : M) :
    IntrinsicPrincipalDensity.weight F g word x = ActualWordMicrolocalBound.realWeight F g word x := by
  induction word generalizing x with
  | nil => rfl
  | cons a word ih => exact congrArg (fun y => g x * y) (ih (F a x))

variable [TopologicalSpace G] [TopologicalSpace M]

/-- Classical local tangent-coordinate continuity suffices; positivity of
the actual unstable volume Jacobian is derived from the derivative word. -/
theorem continuousOn_density (g : M → ℝ)
    (stable unstable : (x : M) → Submodule ℝ (E x)) (N : ℕ) (t s : ℝ)
    (ht : 0 ≤ t) (hs : s ≤ 0) (U : Set ((Fin N → G) × M))
    (hw : ContinuousOn (fun z => weight F g (List.ofFn z.1) z.2) U)
    (hj : ContinuousOn (fun z => unstableJacobian F E D (List.ofFn z.1) z.2 (unstable z.2)) U)
    (hst : ContinuousOn (fun z => stableFactor F E D (List.ofFn z.1) z.2
      (stable (IntrinsicPrincipalDensity.orbit F (List.ofFn z.1) z.2))) U)
    (hi : ContinuousOn (fun z => inverseFactor F E D (List.ofFn z.1) z.2 (unstable z.2)) U) :
    ContinuousOn (density F E D g stable unstable N t s) U := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hw' := continuousOn_iff_continuous_domRestrict.mp hw
  have hj' := continuousOn_iff_continuous_domRestrict.mp hj
  have hst' := continuousOn_iff_continuous_domRestrict.mp hst
  have hi' := continuousOn_iff_continuous_domRestrict.mp hi
  exact (hw'.div hj' (fun z =>
      (unstableJacobian_pos F E D (List.ofFn z.val.1) z.val.2 (unstable z.val.2)).ne')).mul
    ((hst'.rpow_const (fun _ => Or.inr ht)).max
      (hi'.rpow_const (fun _ => Or.inr (neg_nonneg.mpr hs))))

end LeanShared.ContinuousIntrinsicPrincipalDensity
