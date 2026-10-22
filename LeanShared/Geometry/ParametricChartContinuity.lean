module
public import LeanShared.Geometry.ChartLocalization
public import LeanShared.Geometry.SupportedChartExtension

/-! Joint continuity of chart zero extensions and chart coordinates depending on a parameter. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace LeanShared.ParametricChartContinuity

variable {E M P : Type*} [NormedAddCommGroup E] [TopologicalSpace M] [T2Space M]
  [TopologicalSpace P] (e : OpenPartialHomeomorph M E)

/-- A zero extension of a parameter family supported in a fixed compact subset of the chart
target is jointly continuous. -/
theorem extension_continuous (h : E × P → ℂ) (hc : Continuous h) {K : Set E} (Kc : IsCompact K)
    (inside : K ⊆ e.target) (supp : ∀ z p, z ∉ K → h (z, p) = 0) :
    Continuous (fun q : M × P => if q.1 ∈ e.source then h (e q.1, q.2) else 0) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x, p⟩
  by_cases hx : x ∈ e.source
  · have cont : ContinuousAt (fun q : M × P => h (e q.1, q.2)) (x, p) :=
      hc.continuousAt.comp (((e.continuousAt hx).comp continuousAt_fst).prodMk continuousAt_snd)
    apply cont.congr
    filter_upwards [(e.open_source.prod isOpen_univ).mem_nhds (show (x, p) ∈ e.source ×ˢ univ from
      ⟨hx, trivial⟩)] with q hq
    exact (ite_eq_left hq.1).symm
  · have imageCompact : IsCompact (e.symm '' K) := Kc.image_of_continuousOn (e.continuousOn_symm.mono inside)
    have outside : x ∉ e.symm '' K := by
      rintro ⟨z, hz, rfl⟩
      exact hx (e.map_target (inside hz))
    apply continuousAt_const.congr
    filter_upwards [(imageCompact.isClosed.isOpen_compl.prod isOpen_univ).mem_nhds
      (show (x, p) ∈ (e.symm '' K)ᶜ ×ˢ univ from ⟨outside, trivial⟩)] with q hq
    split_ifs with hs
    · have : e q.1 ∉ K := fun hk => hq.1 ⟨e q.1, hk, e.left_inv hs⟩
      rw [supp _ _ this]
    · rfl

/-- The chart coordinate of a jointly continuous family is jointly continuous. -/
theorem coordinate_continuous (θ : M → ℂ) (hθ : Continuous θ) (hcompact : HasCompactSupport θ)
    (hsupp : tsupport θ ⊆ e.source) (F : M × P → ℂ) (hF : Continuous F) :
    Continuous (fun q : E × P => ChartLocalization.coordinate e θ (fun x => F (x, q.2)) q.1) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨z, p⟩
  by_cases hz : z ∈ e.target
  · have cont : ContinuousAt (fun q : E × P => θ (e.symm q.1) * F (e.symm q.1, q.2)) (z, p) :=
      (hθ.continuousAt.comp ((e.continuousAt_symm hz).comp continuousAt_fst)).mul
        (hF.continuousAt.comp (((e.continuousAt_symm hz).comp continuousAt_fst).prodMk
          continuousAt_snd))
    apply cont.congr
    filter_upwards [(e.open_target.prod isOpen_univ).mem_nhds (show (z, p) ∈ e.target ×ˢ univ from
      ⟨hz, trivial⟩)] with q hq
    exact (ite_eq_left hq.1).symm
  · have hzc : z ∉ ChartLocalization.localSupport e θ := fun hc =>
      hz (ChartLocalization.localSupport_subset_target e θ hsupp hc)
    apply continuousAt_const.congr
    filter_upwards [((ChartLocalization.localSupport_isCompact e θ hsupp hcompact).isClosed.isOpen_compl.prod
      isOpen_univ).mem_nhds (show (z, p) ∈ (ChartLocalization.localSupport e θ)ᶜ ×ˢ univ from
        ⟨hzc, trivial⟩)] with q hq
    exact (ChartLocalization.coordinate_zero_outside e θ _ q.1 hq.1).symm

end LeanShared.ParametricChartContinuity
