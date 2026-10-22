module

public import LeanShared.Analysis.IntrinsicDistortionRatio
public import LeanShared.Analysis.ContinuousIntrinsicPrincipalDensity

/-! Actual separate microscopic suprema are bounded by the joint
positive-envelope principal density. The original weight may vanish.
Continuity is needed only on the compact valid cylinder fiber. -/

@[expose] public noncomputable section
open Set
namespace LeanShared.IntrinsicPrincipalSuprema
open CylinderPrincipalCoefficient IntrinsicPrincipalDensity

private theorem exists_coefficient_eq_on {P Y : Type*} [TopologicalSpace P]
    [TopologicalSpace Y] [T2Space Y] {K : Set Y} {R : Set (P × Y)}
    (hK : IsCompact K) (hR : IsClosed R) (f : P × Y → ℝ) (p : P)
    (hf : ContinuousOn (fun y => f (p, y)) (fiber K R p))
    (hne : (fiber K R p).Nonempty) (hf0 : ∀ y ∈ fiber K R p, 0 ≤ f (p, y)) :
    ∃ y ∈ fiber K R p, coefficient K R f p = f (p, y) := by
  have hbounded : BddAbove (values K R f p) :=
    (isCompact_singleton.union ((fiber_isCompact hK hR p).image_of_continuousOn hf)).bddAbove
  obtain ⟨y, hy, hmax⟩ := (fiber_isCompact hK hR p).exists_isMaxOn hne hf
  refine ⟨y, hy, le_antisymm ?_ (le_csSup hbounded (Or.inr (mem_image_of_mem _ hy)))⟩
  apply csSup_le (values_nonempty K R f p)
  rintro v (hv | ⟨z, hz, rfl⟩)
  · obtain rfl := mem_singleton_iff.mp hv
    exact hf0 y hy
  · exact hmax hz

variable {G X : Type*} [TopologicalSpace G] [TopologicalSpace X]
  (F : G → X → X) (E : X → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)]
  (D : ∀ a x, E x ≃L[ℝ] E (F a x))
  (stable unstable : ∀ x, Submodule ℝ (E x))

def originalWeight (g : X → ℝ) (N : ℕ) (z : (Fin N → G) × X) : ℝ :=
  weight F g (List.ofFn z.1) z.2

def inverseJacobian (N : ℕ) (z : (Fin N → G) × X) : ℝ :=
  (unstableJacobian F E D (List.ofFn z.1) z.2 (unstable z.2))⁻¹

def hyperbolicity (N : ℕ) (t s : ℝ) (z : (Fin N → G) × X) : ℝ :=
  max ((stableFactor F E D (List.ofFn z.1) z.2
    (stable (orbit F (List.ofFn z.1) z.2))) ^ t)
    ((inverseFactor F E D (List.ofFn z.1) z.2 (unstable z.2)) ^ (-s))

omit [TopologicalSpace G] [TopologicalSpace X] [∀ x, FiniteDimensional ℝ (E x)] in
theorem hyperbolicity_nonnegative (N : ℕ) (t s : ℝ) (z : (Fin N → G) × X) :
    0 ≤ hyperbolicity F E D stable unstable N t s z := by
  have hfactor : 0 ≤ stableFactor F E D (List.ofFn z.1) z.2
      (stable (orbit F (List.ofFn z.1) z.2)) := by
    unfold stableFactor
    exact ContinuousLinearMap.opNorm_nonneg _
  exact le_max_of_le_left (Real.rpow_nonneg hfactor t)

/-- Apply this to each selected outer cylinder. The mixed ratio bound is
constructed from deterministic distortion and nearby-word compactness in
IntrinsicOrbitDistortion and IntrinsicDistortionRatio. -/
theorem three_suprema_le [T2Space X] (g envelope : X → ℝ) (hg : ∀ x, 0 ≤ g x)
    (henv : ∀ x, 0 < envelope x) (N : ℕ) (t s : ℝ) (word : Fin N → G)
    (K : Set X) (hK : IsCompact K) (R : Set ((Fin N → G) × X)) (hR : IsClosed R)
    (hw : ContinuousOn (fun x => originalWeight F g N (word, x)) (fiber K R word))
    (he : ContinuousOn (fun x => originalWeight F envelope N (word, x)) (fiber K R word))
    (hj : ContinuousOn (fun x => unstableJacobian F E D (List.ofFn word) x (unstable x)) (fiber K R word))
    (hh : ContinuousOn (fun x => hyperbolicity F E D stable unstable N t s (word, x)) (fiber K R word))
    (C : ℝ) (hC : 0 ≤ C)
    (hratio : ∀ x ∈ fiber K R word, ∀ y ∈ fiber K R word, ∀ z ∈ fiber K R word,
      IntrinsicDistortionRatio.ratio F E D unstable g envelope N (word, (x, y, z)) ≤ C) :
    coefficient K R (originalWeight F g N) word *
      coefficient K R (inverseJacobian F E D unstable N) word *
      coefficient K R (hyperbolicity F E D stable unstable N t s) word ≤
      C * coefficient K R (density F E D envelope stable unstable N t s) word := by
  have hjinv : ContinuousOn (fun x => inverseJacobian F E D unstable N (word, x)) (fiber K R word) :=
    hj.inv₀ (fun x _ => (unstableJacobian_pos F E D _ _ _).ne')
  by_cases hne : (fiber K R word).Nonempty
  · obtain ⟨x, hx, hcx⟩ := exists_coefficient_eq_on hK hR _ word hw hne
      (fun x _ => weight_nonneg F g hg _ _)
    obtain ⟨y, hy, hcy⟩ := exists_coefficient_eq_on hK hR _ word hjinv hne
      (fun y _ => inv_nonneg.mpr (unstableJacobian_pos F E D _ _ _).le)
    obtain ⟨z, hz, hcz⟩ := exists_coefficient_eq_on hK hR _ word hh hne
      (fun z _ => hyperbolicity_nonnegative F E D stable unstable N t s _)
    have henvz := IntrinsicDistortionRatio.weight_positive F envelope henv (List.ofFn word) z
    have hjy := unstableJacobian_pos F E D (List.ofFn word) y (unstable y)
    have hjz := unstableJacobian_pos F E D (List.ofFn word) z (unstable z)
    have hpoint : originalWeight F g N (word, x) * inverseJacobian F E D unstable N (word, y) ≤
        C * (originalWeight F envelope N (word, z) * inverseJacobian F E D unstable N (word, z)) := by
      have hnum := (div_le_iff₀ (mul_pos hjy henvz)).mp (hratio x hx y hy z hz)
      change weight F g (List.ofFn word) x / unstableJacobian F E D (List.ofFn word) y (unstable y) ≤
        C * (weight F envelope (List.ofFn word) z / unstableJacobian F E D (List.ofFn word) z (unstable z))
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hjy hjz).mpr
      exact hnum.trans_eq (by ring)
    have hd : ContinuousOn (fun x => density F E D envelope stable unstable N t s (word, x)) (fiber K R word) :=
      (he.div hj (fun x _ => (unstableJacobian_pos F E D _ _ _).ne')).mul hh
    have hbounded : BddAbove (values K R (density F E D envelope stable unstable N t s) word) :=
      (isCompact_singleton.union ((fiber_isCompact hK hR word).image_of_continuousOn hd)).bddAbove
    rw [hcx, hcy, hcz]
    calc
      _ ≤ (C * (originalWeight F envelope N (word, z) * inverseJacobian F E D unstable N (word, z))) *
          hyperbolicity F E D stable unstable N t s (word, z) :=
        mul_le_mul_of_nonneg_right hpoint (hyperbolicity_nonnegative F E D stable unstable N t s _)
      _ = C * density F E D envelope stable unstable N t s (word, z) := by
        simp only [density, principalDensity, originalWeight, inverseJacobian, hyperbolicity, div_eq_mul_inv]
        ring
      _ ≤ C * coefficient K R (density F E D envelope stable unstable N t s) word :=
        mul_le_mul_of_nonneg_left (le_csSup hbounded (Or.inr (mem_image_of_mem _ hz))) hC
  · have hempty := Set.not_nonempty_iff_eq_empty.mp hne
    simp [coefficient, values, hempty]

end LeanShared.IntrinsicPrincipalSuprema
