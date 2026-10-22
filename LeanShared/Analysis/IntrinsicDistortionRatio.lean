module

public import LeanShared.Analysis.IntrinsicPrincipalDensity
public import LeanShared.Analysis.DomainCylinderCoefficient
public import LeanShared.Analysis.RobustTwoNormBlock

/-! The actual separated weight/Jacobian ratio. A deterministic bound on
closed full cylinders gives a common nearby-word bound, with the fixed
constant D+1 independent of the selected word length. Only ordinary local
continuity of the actual weight and Jacobian scalar fields is needed. -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.IntrinsicDistortionRatio
open CylinderPrincipalCoefficient
variable {G X : Type*} [TopologicalSpace G] [TopologicalSpace X]
  (F : G → X → X) (E : X → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)]
  (D : ∀ a x, E x ≃L[ℝ] E (F a x))
  (unstable : ∀ x, Submodule ℝ (E x))

/-- Actual mixed three-point ratio; the envelope occurs only in the
positive denominator, so the original transfer weight may vanish. -/
def ratio (g envelope : X → ℝ) (N : ℕ) (z : (Fin N → G) × (X × X × X)) : ℝ :=
  IntrinsicPrincipalDensity.weight F g (List.ofFn z.1) z.2.1 *
    IntrinsicPrincipalDensity.unstableJacobian F E D (List.ofFn z.1) z.2.2.2 (unstable z.2.2.2) /
      (IntrinsicPrincipalDensity.unstableJacobian F E D (List.ofFn z.1) z.2.2.1 (unstable z.2.2.1) *
        IntrinsicPrincipalDensity.weight F envelope (List.ofFn z.1) z.2.2.2)

omit [TopologicalSpace G] [TopologicalSpace X] in
theorem weight_positive (envelope : X → ℝ) (hpos : ∀ x, 0 < envelope x)
    (word : List G) (x : X) : 0 < IntrinsicPrincipalDensity.weight F envelope word x := by
  induction word generalizing x with
  | nil => exact zero_lt_one
  | cons a word ih => exact mul_pos (hpos x) (ih (F a x))

def tripleRelation {P X : Type*} (R : Set (P × X)) : Set (P × (X × X × X)) :=
  {z | (z.1, z.2.1) ∈ R ∧ (z.1, z.2.2.1) ∈ R ∧ (z.1, z.2.2.2) ∈ R}

omit [TopologicalSpace G] [TopologicalSpace X]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [∀ x, FiniteDimensional ℝ (E x)] in
theorem tripleRelation_closed {P Y : Type*} [TopologicalSpace P] [TopologicalSpace Y]
    {R : Set (P × Y)} (hR : IsClosed R) : IsClosed (tripleRelation R) :=
  (hR.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).inter
    ((hR.preimage (continuous_fst.prodMk (continuous_fst.comp (continuous_snd.comp continuous_snd)))).inter
      (hR.preimage (continuous_fst.prodMk (continuous_snd.comp (continuous_snd.comp continuous_snd)))))

/-- The intrinsic ratio is continuous wherever its four actual scalar
factors are continuous. Jacobian positivity is proved from injectivity of
the genuine derivative word, and positive envelope weights are constructed. -/
theorem continuousOn_ratio (g envelope : X → ℝ) (henv : ∀ x, 0 < envelope x) (N : ℕ)
    (A : Set ((Fin N → G) × (X × X × X)))
    (hw : ContinuousOn (fun z : (Fin N → G) × (X × X × X) =>
      IntrinsicPrincipalDensity.weight F g (List.ofFn z.1) z.2.1) A)
    (hjz : ContinuousOn (fun z : (Fin N → G) × (X × X × X) =>
      IntrinsicPrincipalDensity.unstableJacobian F E D (List.ofFn z.1) z.2.2.2 (unstable z.2.2.2)) A)
    (hjy : ContinuousOn (fun z : (Fin N → G) × (X × X × X) =>
      IntrinsicPrincipalDensity.unstableJacobian F E D (List.ofFn z.1) z.2.2.1 (unstable z.2.2.1)) A)
    (he : ContinuousOn (fun z : (Fin N → G) × (X × X × X) =>
      IntrinsicPrincipalDensity.weight F envelope (List.ofFn z.1) z.2.2.2) A) :
    ContinuousOn (ratio F E D unstable g envelope N) A := by
  exact (hw.mul hjz).div (hjy.mul he) (fun z _ => mul_ne_zero
    (IntrinsicPrincipalDensity.unstableJacobian_pos F E D _ _ _).ne'
    (weight_positive F envelope henv _ _).ne')

/-- Compact triples and a closed moving full cylinder turn a cited
DETERMINISTIC distortion bound into the required random fixed-block bound.
No random distortion constant or arbitrary coefficient USC is an input. -/
theorem exists_nearby_bound [T2Space X] (g envelope : X → ℝ) (N : ℕ) (reference : G)
    (K : Set X) (hK : IsCompact K) (R : Set ((Fin N → G) × X)) (hR : IsClosed R)
    (U : Set (Fin N → G)) (hU : IsOpen U) (href : (fun _ => reference) ∈ U)
    (hf : ContinuousOn (ratio F E D unstable g envelope N)
      ((U ×ˢ univ) ∩ tripleRelation R))
    (C : ℝ) (hC : 0 ≤ C)
    (hdet : ∀ x ∈ fiber K R (fun _ => reference), ∀ y ∈ fiber K R (fun _ => reference),
      ∀ z ∈ fiber K R (fun _ => reference),
        ratio F E D unstable g envelope N ((fun _ => reference), (x, y, z)) ≤ C) :
    ∃ W : Set G, IsOpen W ∧ reference ∈ W ∧
      ∀ word : Fin N → G, (∀ i, word i ∈ W) →
        ∀ x ∈ fiber K R word, ∀ y ∈ fiber K R word, ∀ z ∈ fiber K R word,
          ratio F E D unstable g envelope N (word, (x, y, z)) < C + 1 := by
  let K₃ := K ×ˢ (K ×ˢ K)
  let R₃ := tripleRelation R
  let f := ratio F E D unstable g envelope N
  have hK₃ : IsCompact K₃ := hK.prod (hK.prod hK)
  have hR₃ : IsClosed R₃ := tripleRelation_closed hR
  have hcompact (word : Fin N → G) (hw : word ∈ U) : IsCompact (values K₃ R₃ f word) := by
    apply isCompact_singleton.union
    apply (fiber_isCompact hK₃ hR₃ word).image_of_continuousOn
    exact hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx => ⟨⟨hw, mem_univ _⟩, hx.2⟩)
  have hbase : coefficient K₃ R₃ f (fun _ => reference) ≤ C := by
    apply csSup_le (values_nonempty K₃ R₃ f _)
    rintro v (hv | ⟨xyz, hxyz, rfl⟩)
    · obtain rfl := mem_singleton_iff.mp hv
      exact hC
    · exact hdet xyz.1 ⟨hxyz.1.1, hxyz.2.1⟩ xyz.2.1
        ⟨hxyz.1.2.1, hxyz.2.2.1⟩ xyz.2.2 ⟨hxyz.1.2.2, hxyz.2.2.2⟩
  have hsmall : {word | coefficient K₃ R₃ f word < C + 1} ∈ 𝓝 (fun _ => reference) :=
    DomainCylinderCoefficient.upperSemicontinuousAt_coefficient_on_neighborhood
      hK₃ hR₃ U hU _ href hf (C + 1) (by
        change coefficient K₃ R₃ f (fun _ => reference) < C + 1
        exact hbase.trans_lt (lt_add_one C))
  obtain ⟨W, hW, hrefW, hbox⟩ := RobustTwoNormBlock.exists_open_box_of_mem_nhds
    N reference (U ∩ {word | coefficient K₃ R₃ f word < C + 1})
    (inter_mem (hU.mem_nhds href) hsmall)
  refine ⟨W, hW, hrefW, ?_⟩
  intro word hw x hx y hy z hz
  have hxyz : (x, y, z) ∈ fiber K₃ R₃ word :=
    ⟨⟨hx.1, hy.1, hz.1⟩, hx.2, hy.2, hz.2⟩
  exact (le_csSup (hcompact word (hbox word hw).1).bddAbove
    (Or.inr (mem_image_of_mem _ hxyz))).trans_lt (hbox word hw).2

end LeanShared.IntrinsicDistortionRatio
