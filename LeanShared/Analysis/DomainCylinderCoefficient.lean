module

public import LeanShared.Analysis.CylinderPrincipalCoefficient

/-! # Moving-cylinder coefficients need continuity only on the valid domain

The scalar density of a chart inverse need not be continuous outside its
valid cylinder. Relative continuity on the closed cylinder suffices for the
compact-fiber maximum and its upper semicontinuity, including empty fibers.
-/

@[expose] public noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace LeanShared.DomainCylinderCoefficient
open CylinderPrincipalCoefficient
variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
  {K : Set X} {R : Set (P × X)} {f : P × X → ℝ}

theorem values_isCompact_on (hK : IsCompact K) (hR : IsClosed R)
    (hf : ContinuousOn f R) (p : P) : IsCompact (values K R f p) := by
  apply isCompact_singleton.union
  apply (fiber_isCompact hK hR p).image_of_continuousOn
  exact hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => hx.2)

theorem coefficient_nonneg_on (hK : IsCompact K) (hR : IsClosed R)
    (hf : ContinuousOn f R) (p : P) : 0 ≤ coefficient K R f p :=
  le_csSup (values_isCompact_on hK hR hf p).bddAbove (Or.inl (mem_singleton 0))

theorem density_le_coefficient_on (hK : IsCompact K) (hR : IsClosed R)
    (hf : ContinuousOn f R) (p : P) (x : X) (hx : x ∈ fiber K R p) :
    f (p, x) ≤ coefficient K R f p :=
  le_csSup (values_isCompact_on hK hR hf p).bddAbove
    (Or.inr (mem_image_of_mem _ hx))

theorem upperSemicontinuous_coefficient_on (hK : IsCompact K) (hR : IsClosed R)
    (hf : ContinuousOn f R) : UpperSemicontinuous (coefficient K R f) := by
  intro p r hr
  have hzero : 0 < r := (coefficient_nonneg_on hK hR hf p).trans_lt hr
  obtain ⟨U, hU, heq⟩ := continuousOn_iff'.mp hf (Iio r) isOpen_Iio
  let O := Rᶜ ∪ U
  have hO : IsOpen O := hR.isOpen_compl.union hU
  have he (z : P × X) (hz : z ∈ R) : z ∈ U ↔ f z < r := by
    have h := Set.ext_iff.mp heq z
    simpa only [mem_inter_iff, mem_preimage, mem_Iio, hz, and_true] using h.symm
  have hsub : ({p} : Set P) ×ˢ K ⊆ O := by
    rintro ⟨q, x⟩ ⟨hq, hx⟩
    have hqp : q = p := mem_singleton_iff.mp hq
    subst q
    by_cases hpx : (p, x) ∈ R
    · exact Or.inr ((he (p, x) hpx).mpr
        ((density_le_coefficient_on hK hR hf p x ⟨hx, hpx⟩).trans_lt hr))
    · exact Or.inl hpx
  obtain ⟨V, W, hV, _, hpV, hKW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton hK hO hsub
  filter_upwards [hV.mem_nhds (singleton_subset_iff.mp hpV)] with q hq
  have hh := (values_isCompact_on hK hR hf q).sSup_lt_iff_of_continuous
    (values_nonempty K R f q) continuous_id.continuousOn r
  rw [image_id] at hh
  change coefficient K R f q < r ↔ _ at hh
  apply hh.mpr
  rintro y (hy | ⟨x, hx, rfl⟩)
  · obtain rfl := mem_singleton_iff.mp hy
    exact hzero
  · have hh := hVW (mk_mem_prod hq (hKW hx.1))
    exact (he (q, x) hx.2).mp (hh.resolve_left (not_not.mpr hx.2))

/-- Only a neighborhood of the deterministic parameter needs valid chart
inverses. Outside this neighborhood the total extensions are unrestricted. -/
theorem upperSemicontinuousAt_coefficient_on_neighborhood
    (hK : IsCompact K) (hR : IsClosed R) (U : Set P) (hU : IsOpen U)
    (p : P) (hp : p ∈ U) (hf : ContinuousOn f ((U ×ˢ univ) ∩ R)) :
    UpperSemicontinuousAt (coefficient K R f) p := by
  have hcompact (q : P) (hq : q ∈ U) : IsCompact (values K R f q) := by
    apply isCompact_singleton.union
    apply (fiber_isCompact hK hR q).image_of_continuousOn
    exact hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx => ⟨⟨hq, mem_univ _⟩, hx.2⟩)
  intro r hr
  have hzero : 0 < r :=
    (le_csSup (hcompact p hp).bddAbove (Or.inl (mem_singleton 0))).trans_lt hr
  obtain ⟨V, hV, heq⟩ := continuousOn_iff'.mp hf (Iio r) isOpen_Iio
  let O := (U ×ˢ univ) ∩ (Rᶜ ∪ V)
  have hO : IsOpen O := (hU.prod isOpen_univ).inter (hR.isOpen_compl.union hV)
  have he (z : P × X) (hz : z ∈ (U ×ˢ univ) ∩ R) : z ∈ V ↔ f z < r := by
    have h := Set.ext_iff.mp heq z
    simpa only [mem_inter_iff, mem_preimage, mem_Iio, hz, and_true] using h.symm
  have hsub : ({p} : Set P) ×ˢ K ⊆ O := by
    rintro ⟨q, x⟩ ⟨hq, hx⟩
    have hqp : q = p := mem_singleton_iff.mp hq
    subst q
    refine ⟨⟨hp, mem_univ _⟩, ?_⟩
    by_cases hpx : (p, x) ∈ R
    · apply Or.inr
      apply (he (p, x) ⟨⟨hp, mem_univ _⟩, hpx⟩).mpr
      exact (le_csSup (hcompact p hp).bddAbove
        (Or.inr (mem_image_of_mem _ (show x ∈ fiber K R p from ⟨hx, hpx⟩)))).trans_lt hr
    · exact Or.inl hpx
  obtain ⟨Vtube, W, hVtube, _, hpV, hKW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton hK hO hsub
  filter_upwards [hU.mem_nhds hp, hVtube.mem_nhds (singleton_subset_iff.mp hpV)] with q hqU hq
  have hh := (hcompact q hqU).sSup_lt_iff_of_continuous
    (values_nonempty K R f q) continuous_id.continuousOn r
  rw [image_id] at hh
  change coefficient K R f q < r ↔ _ at hh
  apply hh.mpr
  rintro y (hy | ⟨x, hx, rfl⟩)
  · obtain rfl := mem_singleton_iff.mp hy
    exact hzero
  · have hh := hVW (mk_mem_prod hq (hKW hx.1))
    exact (he (q, x) ⟨⟨hqU, mem_univ _⟩, hx.2⟩).mp
      (hh.2.resolve_left (not_not.mpr hx.2))


/-- A selected finite cover has a common local upper threshold, with no
validity or continuity assumption away from the parameter neighborhood. -/
theorem upperSemicontinuousAt_coverSum_on_neighborhood {I : Type*}
    (cover : Finset I) (R : I → Set (P × X)) (f : I → P × X → ℝ)
    (hK : IsCompact K) (hR : ∀ i ∈ cover, IsClosed (R i))
    (U : Set P) (hU : IsOpen U) (p : P) (hp : p ∈ U)
    (hf : ∀ i ∈ cover, ContinuousOn (f i) ((U ×ˢ univ) ∩ R i)) :
    UpperSemicontinuousAt (fun q => ∑ i ∈ cover, coefficient K (R i) (f i) q) p :=
  upperSemicontinuousAt_sum fun i hi =>
    upperSemicontinuousAt_coefficient_on_neighborhood hK (hR i hi) U hU p hp (hf i hi)


end LeanShared.DomainCylinderCoefficient
