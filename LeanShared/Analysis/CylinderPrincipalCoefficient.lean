module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Principal coefficients on moving closed cylinders

Finite-word anisotropic estimates use suprema of weighted expansion factors
on orbit cylinders. These cylinders vary with the word. Compact ambient
domains and a closed cylinder relation produce upper semicontinuity; fixed
domains or continuity of the moving maximum are not assumed. Zero is adjoined
to give the correct coefficient for empty cylinders.

This file proves the robustness mechanism for the actual
moving-domain supremum rather than accepting its semicontinuity as an input.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology
open scoped BigOperators

namespace LeanShared.CylinderPrincipalCoefficient

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]

section NoiseWords

variable {G : Type*} [TopologicalSpace G]

/-- Actual chronological prefix orbit of a finite word. Past its length the
orbit is kept constant; only indices smaller than the length are used. -/
def prefixOrbit (F : G → X → X) {N : ℕ} (word : Fin N → G) : ℕ → X → X
  | 0, x => x
  | k + 1, x => if h : k < N then F (word ⟨k, h⟩) (prefixOrbit F word k x)
    else prefixOrbit F word k x

theorem continuous_prefixOrbit (F : G → X → X)
    (hF : Continuous (fun z : G × X => F z.1 z.2)) (N k : ℕ) :
    Continuous (fun z : (Fin N → G) × X => prefixOrbit F z.1 k z.2) := by
  induction k with
  | zero => exact continuous_snd
  | succ k ih =>
    by_cases hk : k < N
    · simpa only [prefixOrbit, dite_eq_left hk, Function.comp_def] using
        hF.comp (((continuous_apply ⟨k, hk⟩).comp continuous_fst).prodMk ih)
    · simpa only [prefixOrbit, dite_eq_right hk] using ih

/-- Absolute accumulated weight along the literal successive random maps. -/
def wordWeight (F : G → X → X) (g : X → ℝ) {N : ℕ} :
    (Fin N → G) × X → ℝ := fun z =>
  ∏ j : Fin N, |g (prefixOrbit F z.1 j.val z.2)|

theorem continuous_wordWeight (F : G → X → X) (g : X → ℝ)
    (hF : Continuous (fun z : G × X => F z.1 z.2)) (hg : Continuous g) (N : ℕ) :
    Continuous (wordWeight F g (N := N)) :=
  continuous_finsetProd _ fun j _ => (hg.comp (continuous_prefixOrbit F hF N j.val)).abs

end NoiseWords

def fiber (K : Set X) (R : Set (P × X)) (p : P) : Set X :=
  K ∩ (fun x => (p, x)) ⁻¹' R

def values (K : Set X) (R : Set (P × X)) (f : P × X → ℝ) (p : P) : Set ℝ :=
  {0} ∪ (fun x => f (p, x)) '' fiber K R p

def coefficient (K : Set X) (R : Set (P × X)) (f : P × X → ℝ) (p : P) : ℝ :=
  sSup (values K R f p)

variable {K : Set X} {R : Set (P × X)} {f : P × X → ℝ}

theorem fiber_isCompact (hK : IsCompact K) (hR : IsClosed R) (p : P) :
    IsCompact (fiber K R p) :=
  hK.inter_right (hR.preimage (continuous_const.prodMk continuous_id))

theorem values_isCompact (hK : IsCompact K) (hR : IsClosed R)
    (hf : Continuous f) (p : P) : IsCompact (values K R f p) :=
  isCompact_singleton.union ((fiber_isCompact hK hR p).image
    (hf.comp (continuous_const.prodMk continuous_id)))

omit [TopologicalSpace P] [TopologicalSpace X] in
theorem values_nonempty (K : Set X) (R : Set (P × X)) (f : P × X → ℝ) (p : P) :
    (values K R f p).Nonempty := ⟨0, Or.inl (mem_singleton 0)⟩

theorem coefficient_nonneg (hK : IsCompact K) (hR : IsClosed R)
    (hf : Continuous f) (p : P) : 0 ≤ coefficient K R f p :=
  le_csSup (values_isCompact hK hR hf p).bddAbove (Or.inl (mem_singleton 0))

theorem density_le_coefficient (hK : IsCompact K) (hR : IsClosed R)
    (hf : Continuous f) (p : P) (x : X) (hx : x ∈ fiber K R p) :
    f (p, x) ≤ coefficient K R f p :=
  le_csSup (values_isCompact hK hR hf p).bddAbove
    (Or.inr (mem_image_of_mem _ hx))

/-- The upper threshold of the moving maximum is an open condition. The
tube argument includes points that leave the cylinder, and empty fibers. -/
theorem upperSemicontinuous_coefficient (hK : IsCompact K) (hR : IsClosed R)
    (hf : Continuous f) : UpperSemicontinuous (coefficient K R f) := by
  intro p r hr
  have hzero : 0 < r := (coefficient_nonneg hK hR hf p).trans_lt hr
  let O : Set (P × X) := Rᶜ ∪ f ⁻¹' Iio r
  have hO : IsOpen O := hR.isOpen_compl.union (isOpen_Iio.preimage hf)
  have hsub : ({p} : Set P) ×ˢ K ⊆ O := by
    rintro ⟨q, x⟩ ⟨hq, hx⟩
    have hqp : q = p := mem_singleton_iff.mp hq
    subst q
    by_cases hpx : (p, x) ∈ R
    · exact Or.inr ((density_le_coefficient hK hR hf p x ⟨hx, hpx⟩).trans_lt hr)
    · exact Or.inl hpx
  obtain ⟨U, V, hU, _, hpU, hKV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hK hO hsub
  filter_upwards [hU.mem_nhds (singleton_subset_iff.mp hpU)] with q hq
  have hh := (values_isCompact hK hR hf q).sSup_lt_iff_of_continuous
    (values_nonempty K R f q) continuous_id.continuousOn r
  rw [image_id] at hh
  change coefficient K R f q < r ↔ _ at hh
  apply hh.mpr
  intro y hy
  change y < r
  rcases hy with hy | ⟨x, hx, rfl⟩
  · obtain rfl := mem_singleton_iff.mp hy
    exact hzero
  · have hh := hUV (mk_mem_prod hq (hKV hx.1))
    exact hh.resolve_left (not_not.mpr hx.2)

/-- Closed orbit-cylinder relations are produced from actual continuous
prefix orbits and closed chart domains. -/
def orbitCylinder {J : Type*} (orbit : J → P × X → X) (chart : J → Set X) :
    Set (P × X) := {z | ∀ j, orbit j z ∈ chart j}

theorem orbitCylinder_isClosed {J : Type*} (orbit : J → P × X → X)
    (chart : J → Set X) (horbit : ∀ j, Continuous (orbit j))
    (hchart : ∀ j, IsClosed (chart j)) : IsClosed (orbitCylinder orbit chart) := by
  have heq : orbitCylinder orbit chart = ⋂ j, (orbit j) ⁻¹' chart j := by
    ext z
    simp [orbitCylinder]
  rw [heq]
  exact isClosed_iInter fun j => (hchart j).preimage (horbit j)

/-- The literal local principal density: accumulated absolute weight,
inverse unstable Jacobian, and the larger of the stable/unstable losses.
The unstable factor is the norm of the inverse derivative, so its exponent
is `-s`, rather than the negative power of a possibly zero expansion. -/
def principalDensity (weight jac stable unstableInv : P × X → ℝ) (t s : ℝ) :
    P × X → ℝ := fun z =>
  weight z / jac z * max (stable z ^ t) (unstableInv z ^ (-s))

theorem continuous_principalDensity (weight jac stable unstableInv : P × X → ℝ)
    (hw : Continuous weight) (hj : Continuous jac) (hs : Continuous stable)
    (hu : Continuous unstableInv) (hjac : ∀ z, jac z ≠ 0)
    (t s : ℝ) (ht : 0 ≤ t) (hsign : s ≤ 0) :
    Continuous (principalDensity weight jac stable unstableInv t s) :=
  (hw.div hj hjac).mul
    ((hs.rpow_const (fun _ => Or.inr ht)).max
      (hu.rpow_const (fun _ => Or.inr (neg_nonneg.mpr hsign))))

theorem upperSemicontinuous_principalCylinder
    (weight jac stable unstableInv : P × X → ℝ)
    (hw : Continuous weight) (hj : Continuous jac) (hs : Continuous stable)
    (hu : Continuous unstableInv) (hjac : ∀ z, jac z ≠ 0)
    (t s : ℝ) (ht : 0 ≤ t) (hsign : s ≤ 0)
    {J : Type*} (orbit : J → P × X → X) (chart : J → Set X)
    (horbit : ∀ j, Continuous (orbit j)) (hchart : ∀ j, IsClosed (chart j))
    (hK : IsCompact K) :
    UpperSemicontinuous (coefficient K (orbitCylinder orbit chart)
      (principalDensity weight jac stable unstableInv t s)) :=
  upperSemicontinuous_coefficient hK (orbitCylinder_isClosed orbit chart horbit hchart)
    (continuous_principalDensity weight jac stable unstableInv hw hj hs hu hjac t s ht hsign)

/-- A selected finite cylinder cover gives an upper semicontinuous
principal coefficient. No minimum over changing subcovers is taken. -/
theorem upperSemicontinuous_coverSum {I : Type*} (cover : Finset I)
    (R : I → Set (P × X)) (f : I → P × X → ℝ)
    (hK : IsCompact K) (hR : ∀ i ∈ cover, IsClosed (R i))
    (hf : ∀ i ∈ cover, Continuous (f i)) :
    UpperSemicontinuous (fun p => ∑ i ∈ cover, coefficient K (R i) (f i) p) :=
  upperSemicontinuous_sum fun i hi => upperSemicontinuous_coefficient hK (hR i hi) (hf i hi)

/-- Cylinder distortion converts the product of separate suprema in the
microlocal estimate into the joint supremum used in pressure. This does not
assume positive weight; the explicit distortion inequality is essential. -/
theorem coefficient_mul_le_of_distortion (hK : IsCompact K) (hR : IsClosed R)
    (a h : P × X → ℝ) (ha : Continuous a) (hh : Continuous h) (p : P)
    (D : ℝ) (hD : 0 ≤ D)
    (ha0 : ∀ x ∈ fiber K R p, 0 ≤ a (p, x))
    (hh0 : ∀ x ∈ fiber K R p, 0 ≤ h (p, x))
    (hdist : ∀ x ∈ fiber K R p, ∀ y ∈ fiber K R p,
      a (p, x) ≤ D * a (p, y)) :
    coefficient K R a p * coefficient K R h p ≤
      D * coefficient K R (fun z => a z * h z) p := by
  by_cases hne : (fiber K R p).Nonempty
  · obtain ⟨y, hy, hmax⟩ := (fiber_isCompact hK hR p).exists_isMaxOn hne
      (hh.comp (continuous_const.prodMk continuous_id)).continuousOn
    have hhcoef : coefficient K R h p = h (p, y) := by
      apply le_antisymm
      · apply csSup_le (values_nonempty K R h p)
        rintro z (hz | ⟨x, hx, rfl⟩)
        · obtain rfl := mem_singleton_iff.mp hz
          exact hh0 y hy
        · exact hmax hx
      · exact density_le_coefficient hK hR hh p y hy
    have hacoef : coefficient K R a p ≤ D * a (p, y) := by
      apply csSup_le (values_nonempty K R a p)
      rintro z (hz | ⟨x, hx, rfl⟩)
      · obtain rfl := mem_singleton_iff.mp hz
        exact mul_nonneg hD (ha0 y hy)
      · exact hdist x hx y hy
    rw [hhcoef]
    calc
      coefficient K R a p * h (p, y) ≤ (D * a (p, y)) * h (p, y) :=
        mul_le_mul_of_nonneg_right hacoef (hh0 y hy)
      _ = D * (a (p, y) * h (p, y)) := mul_assoc _ _ _
      _ ≤ D * coefficient K R (fun z => a z * h z) p :=
        mul_le_mul_of_nonneg_left (density_le_coefficient hK hR (ha.mul hh) p y hy) hD
  · have hempty := Set.not_nonempty_iff_eq_empty.mp hne
    simp [coefficient, values, hempty]

theorem exists_coefficient_eq (hK : IsCompact K) (hR : IsClosed R)
    (ha : Continuous f) (p : P) (hne : (fiber K R p).Nonempty)
    (ha0 : ∀ x ∈ fiber K R p, 0 ≤ f (p, x)) :
    ∃ y ∈ fiber K R p, coefficient K R f p = f (p, y) := by
  obtain ⟨y, hy, hmax⟩ := (fiber_isCompact hK hR p).exists_isMaxOn hne
    (ha.comp (continuous_const.prodMk continuous_id)).continuousOn
  refine ⟨y, hy, le_antisymm ?_ (density_le_coefficient hK hR ha p y hy)⟩
  apply csSup_le (values_nonempty K R f p)
  rintro z (hz | ⟨x, hx, rfl⟩)
  · obtain rfl := mem_singleton_iff.mp hz
    exact ha0 y hy
  · exact hmax hx

/-- Source-exact bounded distortion: any separated weight/Jacobian values
are bounded by the ratio at every point in the same cylinder. It converts
the three separate suprema in the local operator bound into pressure's joint
supremum without requiring the hyperbolicity factor to have bounded distortion. -/
theorem three_coefficients_le_of_ratio_distortion (hK : IsCompact K) (hR : IsClosed R)
    (weight invJac hyp : P × X → ℝ)
    (hw : Continuous weight) (hj : Continuous invJac) (hh : Continuous hyp)
    (p : P) (D : ℝ) (hD : 0 ≤ D)
    (hw0 : ∀ x ∈ fiber K R p, 0 ≤ weight (p, x))
    (hj0 : ∀ x ∈ fiber K R p, 0 ≤ invJac (p, x))
    (hh0 : ∀ x ∈ fiber K R p, 0 ≤ hyp (p, x))
    (hdist : ∀ x ∈ fiber K R p, ∀ y ∈ fiber K R p, ∀ z ∈ fiber K R p,
      weight (p, x) * invJac (p, y) ≤ D * (weight (p, z) * invJac (p, z))) :
    coefficient K R weight p * coefficient K R invJac p * coefficient K R hyp p ≤
      D * coefficient K R (fun z => weight z * invJac z * hyp z) p := by
  by_cases hne : (fiber K R p).Nonempty
  · obtain ⟨x, hx, hcx⟩ := exists_coefficient_eq hK hR hw p hne hw0
    obtain ⟨y, hy, hcy⟩ := exists_coefficient_eq hK hR hj p hne hj0
    obtain ⟨z, hz, hcz⟩ := exists_coefficient_eq hK hR hh p hne hh0
    rw [hcx, hcy, hcz]
    calc
      weight (p, x) * invJac (p, y) * hyp (p, z) ≤
          (D * (weight (p, z) * invJac (p, z))) * hyp (p, z) :=
        mul_le_mul_of_nonneg_right (hdist x hx y hy z hz) (hh0 z hz)
      _ = D * (weight (p, z) * invJac (p, z) * hyp (p, z)) := mul_assoc _ _ _
      _ ≤ D * coefficient K R (fun z => weight z * invJac z * hyp z) p :=
        mul_le_mul_of_nonneg_left
          (density_le_coefficient hK hR ((hw.mul hj).mul hh) p z hz) hD
  · have hempty := Set.not_nonempty_iff_eq_empty.mp hne
    simp [coefficient, values, hempty]

/-- A fixed subcover remains valid for nearby words if it covers the
deterministic surviving cylinder by open cylinders. Closed covers alone do
not provide this robustness. -/
theorem exists_robust_subcover (hK : IsCompact K) (hR : IsClosed R)
    (O : Set (P × X)) (hO : IsOpen O) (p : P)
    (hcover : ∀ x ∈ fiber K R p, (p, x) ∈ O) :
    ∃ W : Set P, IsOpen W ∧ p ∈ W ∧
      ∀ q ∈ W, ∀ x ∈ fiber K R q, (q, x) ∈ O := by
  have hsub : ({p} : Set P) ×ˢ K ⊆ Rᶜ ∪ O := by
    rintro ⟨q, x⟩ ⟨hq, hx⟩
    have hqp : q = p := mem_singleton_iff.mp hq
    subst q
    by_cases hpx : (p, x) ∈ R
    · exact Or.inr (hcover x ⟨hx, hpx⟩)
    · exact Or.inl hpx
  obtain ⟨W, V, hW, _, hpW, hKV, hWV⟩ :=
    generalized_tube_lemma isCompact_singleton hK (hR.isOpen_compl.union hO) hsub
  refine ⟨W, hW, singleton_subset_iff.mp hpW, ?_⟩
  intro q hq x hx
  exact (hWV (mk_mem_prod hq (hKV hx.1))).resolve_left (not_not.mpr hx.2)

end LeanShared.CylinderPrincipalCoefficient
