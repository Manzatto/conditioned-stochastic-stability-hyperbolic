module
public import LeanShared.Geometry.ChartLocalization
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! Chart cutoffs for regularized traces. Given smooth chart cutoffs `c_i` summing to one on a
compact set `R` inside an open set `V`, a smooth partition of unity `c'_i` on `R` subordinate to
`{c_i ≠ 0} ∩ V ∩ source_i` gives chart weights `wt_i = (c'_i / c_i) ∘ φ_i⁻¹` (zero extended) with
`c_i · wt_i ∘ φ_i = c'_i`, and chart bumps `cut_i` equal to one on a fixed thickening of
`φ_i(tsupport c'_i)`, supported in `φ_i({c_i ≠ 0} ∩ V)`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Metric Filter Function
open scoped Manifold ContDiff SchwartzMap Topology
namespace LeanShared.TraceChartCutoffs

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]

/-- The zero-extended chart coordinate of `θ f` is smooth when `f` is smooth near `tsupport θ`. -/
theorem coordinate_contDiff_near (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (θ : M → ℂ)
    (hθ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ θ) (hsupp : tsupport θ ⊆ e.source)
    (hcompact : HasCompactSupport θ) (f : M → ℂ)
    (hf : ∀ x ∈ tsupport θ, ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ f x) :
    ContDiff ℝ ∞ (ChartLocalization.coordinate e θ f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ e.target
  · by_cases hin : e.symm x ∈ tsupport θ
    · have hc : ContDiffAt ℝ ∞ (fun y => θ (e.symm y) * f (e.symm y)) x :=
        (((hθ (e.symm x)).comp x (contMDiffAt_symm_of_mem_maximalAtlas he hx)).contDiffAt).mul
          (((hf _ hin).comp x (contMDiffAt_symm_of_mem_maximalAtlas he hx)).contDiffAt)
      apply hc.congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds hx] with y hy
      exact ite_eq_left hy
    · have near : ∀ᶠ y in 𝓝 x, y ∈ e.target ∧ e.symm y ∉ tsupport θ :=
        Filter.Eventually.and (show ∀ᶠ y in 𝓝 x, y ∈ e.target from e.open_target.mem_nhds hx)
          (show ∀ᶠ y in 𝓝 x, e.symm y ∈ (tsupport θ)ᶜ from (e.continuousAt_symm hx).preimage_mem_nhds
            ((isClosed_tsupport θ).isOpen_compl.mem_nhds hin))
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [near] with y hy
      simp [ChartLocalization.coordinate, hy.1, image_eq_zero_of_notMem_tsupport hy.2]
  · have hxc : x ∉ ChartLocalization.localSupport e θ := fun hc =>
      hx (ChartLocalization.localSupport_subset_target e θ hsupp hc)
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [(ChartLocalization.localSupport_isCompact e θ hsupp hcompact).isClosed.isOpen_compl.mem_nhds
      hxc] with y hy
    exact ChartLocalization.coordinate_zero_outside e θ f y hy

/-- The topological support of a chart coordinate lies in the localization support. -/
theorem coordinate_tsupport (e : OpenPartialHomeomorph M E) (θ : M → ℂ)
    (hsupp : tsupport θ ⊆ e.source) (hcompact : HasCompactSupport θ) (f : M → ℂ) :
    tsupport (ChartLocalization.coordinate e θ f) ⊆ ChartLocalization.localSupport e θ :=
  closure_minimal (fun y hy => by
      by_contra h
      exact hy (ChartLocalization.coordinate_zero_outside e θ f y h))
    (ChartLocalization.localSupport_isCompact e θ hsupp hcompact).isClosed

theorem exists_margin {ι : Type*} [Fintype ι] (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ δ i := by
  by_cases hι : Nonempty ι
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty δ,
      (Finset.lt_inf'_iff _).mpr fun i _ => hδ i, fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
  · exact ⟨1, one_pos, fun i => absurd ⟨i⟩ hι⟩

variable {ι : Type*} [Fintype ι] (e : ι → OpenPartialHomeomorph M E)
  (he : ∀ i, e i ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (c : ι → M → ℝ)
  (hc : ∀ i, ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ (c i)) (hcs : ∀ i, tsupport (c i) ⊆ (e i).source)
  {R V : Set M} (hR : IsCompact R) (hV : IsOpen V) (hRV : R ⊆ V) (hsum : ∀ x ∈ R, ∑ i, c i x = 1)

include he hc hcs hR hV hRV hsum in
theorem exists_cutoffs :
    ∃ (c' : ι → M → ℝ) (wt cut : ι → 𝓢(E, ℂ)) (εc : ℝ), 0 < εc ∧
      (∀ i, ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ (c' i)) ∧ (∀ i x, 0 ≤ c' i x) ∧
      (∀ i, tsupport (c' i) ⊆ (e i).source) ∧ (∀ i, tsupport (c' i) ⊆ V) ∧
      (∀ x ∈ R, ∑ i, c' i x = 1) ∧
      (∀ i, ∀ x ∈ (e i).source, (c' i x : ℂ) = (c i x : ℂ) * wt i (e i x)) ∧
      (∀ i, HasCompactSupport (cut i : E → ℂ)) ∧ (∀ i, HasCompactSupport (wt i : E → ℂ)) ∧
      (∀ i, tsupport (cut i : E → ℂ) ⊆ e i '' tsupport (c i)) ∧
      (∀ i, (e i).symm '' tsupport (cut i : E → ℂ) ⊆ V) ∧
      (∀ i, ∀ z ∈ tsupport (wt i : E → ℂ), cut i z = 1) ∧
      (∀ i, ∀ z ∈ (e i).target, c' i ((e i).symm z) ≠ 0 → ∀ u, ‖u - z‖ ≤ εc → cut i u = 1) := by
  classical
  let U : ι → Set M := fun i => {x | c i x ≠ 0} ∩ V ∩ (e i).source
  have hUo : ∀ i, IsOpen (U i) := fun i =>
    ((isOpen_compl_singleton.preimage (hc i).continuous).inter hV).inter (e i).open_source
  have cover : R ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i, c i x ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      have := hsum x hx
      simp [h] at this
    exact mem_iUnion.mpr ⟨i, ⟨hi, hRV hx⟩, hcs i (subset_tsupport _ hi)⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, E)) hR.isClosed U hUo cover
  let c' : ι → M → ℝ := fun i x => f i x
  have c'U : ∀ i, tsupport (c' i) ⊆ U i := hf
  have c'ne : ∀ i x, c' i x ≠ 0 → c i x ≠ 0 := fun i x h =>
    (c'U i (subset_tsupport _ h)).1.1
  -- chart weights
  let θ : ι → M → ℂ := fun i x => (c' i x : ℂ)
  have θsmooth : ∀ i, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (θ i) := fun i =>
    Complex.ofRealCLM.contMDiff.comp (f i).contMDiff
  have θsupp : ∀ i, tsupport (θ i) ⊆ (e i).source := fun i =>
    (tsupport_comp_subset Complex.ofReal_zero (c' i)).trans ((c'U i).trans inter_subset_right)
  have θcompact : ∀ i, HasCompactSupport (θ i) := fun i => HasCompactSupport.of_compactSpace _
  let inv : ι → M → ℂ := fun i x => (((c i x)⁻¹ : ℝ) : ℂ)
  have invSmooth : ∀ i, ∀ x ∈ tsupport (θ i), ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, ℂ)) ∞ (inv i) x :=
    fun i x hx => by
      have hne : c i x ≠ 0 :=
        (c'U i ((tsupport_comp_subset Complex.ofReal_zero (c' i)) hx)).1.1
      exact Complex.ofRealCLM.contMDiff.contMDiffAt.comp x
        (((hc i).contMDiffAt).inv₀ hne)
  let wtf : ι → E → ℂ := fun i => ChartLocalization.coordinate (e i) (θ i) (inv i)
  have wtCompact : ∀ i, HasCompactSupport (wtf i) := fun i =>
    ChartLocalization.coordinate_hasCompactSupport (e i) (θ i) (θsupp i) (θcompact i) (inv i)
  have wtSmooth : ∀ i, ContDiff ℝ ∞ (wtf i) := fun i =>
    coordinate_contDiff_near (e i) (he i) (θ i) (θsmooth i) (θsupp i) (θcompact i) (inv i)
      (invSmooth i)
  let wt : ι → 𝓢(E, ℂ) := fun i => (wtCompact i).toSchwartzMap (wtSmooth i)
  -- chart bumps
  let A : ι → Set E := fun i => e i '' tsupport (c' i)
  have Acompact : ∀ i, IsCompact (A i) := fun i =>
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((e i).continuousOn.mono ((c'U i).trans inter_subset_right))
  let O : ι → Set E := fun i => e i '' U i
  have Oopen : ∀ i, IsOpen (O i) := fun i =>
    (e i).isOpen_image_of_subset_source (hUo i) inter_subset_right
  have AO : ∀ i, A i ⊆ O i := fun i => image_mono (c'U i)
  choose δ δpos δsub using fun i => (Acompact i).exists_cthickening_subset_open (Oopen i) (AO i)
  have bump : ∀ i, ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ range g ⊆ Icc 0 1 ∧
      support g = thickening (δ i) (A i) ∧ (∀ x, x ∈ cthickening (δ i / 2) (A i) ↔ g x = 1) :=
    fun i => exists_contDiff_support_eq_eq_one_iff isOpen_thickening isClosed_cthickening
      (cthickening_subset_thickening' (δpos i) (by linarith [δpos i]) _)
  choose g gSmooth gRange gSupport gOne using bump
  have gTsupport : ∀ i, tsupport (g i) ⊆ O i := fun i => by
    change closure (support (g i)) ⊆ _
    rw [gSupport]
    exact (closure_thickening_subset_cthickening _ _).trans (δsub i)
  let cutf : ι → E → ℂ := fun i z => (g i z : ℂ)
  have cutCompact : ∀ i, HasCompactSupport (cutf i) := fun i =>
    HasCompactSupport.intro ((Acompact i).cthickening (r := δ i)) fun z hz => by
      have : z ∉ support (g i) := by
        rw [gSupport]
        exact fun h => hz (thickening_subset_cthickening _ _ h)
      simp only [cutf, notMem_support.mp this, Complex.ofReal_zero]
  have cutSmooth : ∀ i, ContDiff ℝ ∞ (cutf i) := fun i => Complex.ofRealCLM.contDiff.comp (gSmooth i)
  let cut : ι → 𝓢(E, ℂ) := fun i => (cutCompact i).toSchwartzMap (cutSmooth i)
  have cutTsupport : ∀ i, tsupport (cut i : E → ℂ) ⊆ O i := fun i =>
    (tsupport_comp_subset Complex.ofReal_zero (g i)).trans (gTsupport i)
  obtain ⟨εc, εcpos, εcle⟩ := exists_margin (fun i => δ i / 2) (fun i => by linarith [δpos i])
  refine ⟨c', wt, cut, εc, εcpos, fun i => (f i).contMDiff, fun i x => f.nonneg i x,
    fun i => (c'U i).trans inter_subset_right, fun i => (c'U i).trans
      (inter_subset_left.trans inter_subset_right), fun x hx => ?_, fun i x hx => ?_,
    cutCompact, wtCompact, fun i => ?_, fun i => ?_, fun i z hz => ?_, fun i z hz hne u hu => ?_⟩
  · rw [← finsum_eq_sum_of_fintype]
    exact f.sum_eq_one hx
  · have value : wt i (e i x) = θ i x * inv i x := by
      change ChartLocalization.coordinate (e i) (θ i) (inv i) (e i x) = _
      simp [ChartLocalization.coordinate, (e i).map_source hx, (e i).left_inv hx]
    rw [value]
    by_cases h : c i x = 0
    · have : c' i x = 0 := by
        by_contra h'
        exact c'ne i x h' h
      simp [θ, this, h]
    · have hC : (c i x : ℂ) ≠ 0 := by exact_mod_cast h
      simp only [θ, inv, Complex.ofReal_inv]
      rw [mul_comm (c' i x : ℂ), ← mul_assoc, mul_inv_cancel₀ hC, one_mul]
  · refine (cutTsupport i).trans ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, subset_tsupport _ hy.1.1, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := cutTsupport i hz
    rw [(e i).left_inv hy.2]
    exact hy.1.2
  · have inA : z ∈ A i := by
      have := coordinate_tsupport (e i) (θ i) (θsupp i) (θcompact i) (inv i) hz
      obtain ⟨y, hy, rfl⟩ := this
      exact ⟨y, (tsupport_comp_subset Complex.ofReal_zero (c' i)) hy, rfl⟩
    change ((g i z : ℝ) : ℂ) = 1
    rw [(gOne i z).mp (self_subset_cthickening _ inA), Complex.ofReal_one]
  · have inA : z ∈ A i := ⟨(e i).symm z, subset_tsupport _ hne, (e i).right_inv hz⟩
    have close : u ∈ cthickening (δ i / 2) (A i) :=
      mem_cthickening_of_dist_le u z _ _ inA ((dist_eq_norm u z).le.trans (hu.trans (εcle i)))
    change ((g i u : ℝ) : ℂ) = 1
    rw [(gOne i u).mp close, Complex.ofReal_one]

end LeanShared.TraceChartCutoffs
