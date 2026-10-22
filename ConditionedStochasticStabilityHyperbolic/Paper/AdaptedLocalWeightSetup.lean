module

public import ConditionedStochasticStabilityHyperbolic.Paper.AdaptedAnalysisNeighborhood
public import ConditionedStochasticStabilityHyperbolic.Neighborhoods.TwoSidedAnalysisCollar

/-! A cutoff supported in a small analysis neighborhood retains exact
weight agreement and nonreturn for the original outer closed live state. -/
public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.AdaptedLocalWeightSetup
open LeanShared
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M}
  (h : HL (E := E) T g Λ V) (w : M → ℝ) (W : Set M)

structure Data where
  collar : Set M
  retained : Set M
  cutoff : M → ℝ
  collar_open : IsOpen collar
  core_collar : Λ ⊆ collar
  collar_live : closure collar ⊆ W
  positive : ∀ x ∈ closure collar, 0 < w x ∧ 0 < w (T.symm x)
  retained_open : IsOpen retained
  core_retained : Λ ⊆ retained
  retained_collar : closure retained ⊆ collar
  no_return : (T '' closure retained) ∩ forwardTrapped T (closure V) ⊆ retained
  cutoff_smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ cutoff
  cutoff_support : tsupport cutoff ⊆ collar
  weight_nonnegative : ∀ x, 0 ≤ (cutoff * w) x
  weight_support : tsupport (cutoff * w) ⊆ W
  weight_agreement : EqOn (cutoff * w) w (closure retained)
  core_agreement : EqOn (cutoff * w) g Λ
  fresh : HL (E := E) T (cutoff * w) Λ W
  regularity_eq : fresh.r = h.r
  hyperbolic_eq : fresh.basic.hyperbolic = h.basic.hyperbolic

omit [FiniteDimensional ℝ E] [CompactSpace M] in
include h in
/-- The isolated core of every intermediate analysis neighborhood is
literally the original core; no additional hyperbolic isolation is assumed. -/
theorem analysis_core (hΛW : Λ ⊆ W) (hWV : W ⊆ V) :
    Λ = isolatedCore T (closure W) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxold : x ∈ isolatedCore T (closure V) := h.actual_isolated_core ▸ hx
    exact ⟨fun n => subset_closure (hΛW (h.actual_isolated_core.symm ▸
      iterate_mem_isolatedCore T (closure V) hxold n)),
      fun n => subset_closure (hΛW (h.actual_isolated_core.symm ▸
        iterate_symm_mem_isolatedCore T (closure V) hxold n))⟩
  · intro x hx
    apply h.actual_isolated_core.symm ▸ (show x ∈ isolatedCore T (closure V) from ?_)
    exact ⟨fun n => closure_mono hWV (hx.1 n), fun n => closure_mono hWV (hx.2 n)⟩

/-- The fixed cutoff agrees with the actual departure weight on an open
retained collar, while its entire support lies in the small analysis domain.
Nonreturn is proved relative to the original closed live state. -/
def of_regular (hW : IsOpen W) (hΛW : Λ ⊆ W) (hWV : W ⊆ V)
    (hw : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1) w)
    (agree : EqOn w g Λ)
    (smoothProduct : ∀ ζ : M → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ →
      FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1) (ζ * w)) : Data h w W :=
  Classical.choice (by
    have hwc : Continuous w := hw.differentiable.continuous
    have positive : ∀ x ∈ Λ, 0 < w x := by
      intro x hx
      rw [agree hx]
      exact h.weight_positive x hx
    obtain ⟨G, B, hG, coreG, GW, pos, hB, coreB, BG, noReturn⟩ :=
      exists_twoSided_positive_orbit_collar_inside T V W Λ h.basic.open_neighborhood
        hW h.compact_core h.nonempty_core hΛW hWV h.actual_isolated_core.symm
        w hwc positive
    obtain ⟨ζ, smooth, _, support, _, nonnegative, supportWeight, retained⟩ :=
      SmoothWeightCutoff.exists_weight_cutoff_of_local_nonnegative (E := E)
        (closure B) G isClosed_closure.isCompact hG BG w hwc
        (fun x hx => (pos x (subset_closure hx)).1.le)
    have supported : tsupport (ζ * w) ⊆ W :=
      supportWeight.trans (subset_closure.trans GW)
    have coreAgree : EqOn (ζ * w) g Λ := fun x hx =>
      (retained (subset_closure (coreB hx))).trans (agree hx)
    let fresh : HL (E := E) T (ζ * w) Λ W := {
      r := h.r
      regularity_gt_one := h.regularity_gt_one
      map_regular := h.map_regular
      inverse_regular := h.inverse_regular
      basic := {
        hyperbolic := h.basic.hyperbolic
        nonempty := h.nonempty_core
        open_neighborhood := hW
        subset_neighborhood := hΛW
        isolated := analysis_core h W hΛW hWV
        dense_orbit := h.basic.dense_orbit }
      weight_regular := smoothProduct ζ smooth
      weight_nonnegative := nonnegative
      weight_supported := supported
      weight_positive := fun x hx => (coreAgree hx).symm ▸ h.weight_positive x hx
      mixing := h.mixing }
    exact ⟨{
      collar := G
      retained := B
      cutoff := ζ
      collar_open := hG
      core_collar := coreG
      collar_live := GW
      positive := pos
      retained_open := hB
      core_retained := coreB
      retained_collar := BG
      no_return := noReturn
      cutoff_smooth := smooth
      cutoff_support := support
      weight_nonnegative := nonnegative
      weight_support := supported
      weight_agreement := retained
      core_agreement := coreAgree
      fresh := fresh
      regularity_eq := rfl
      hyperbolic_eq := rfl }⟩)

namespace Data
variable (s : Data h w W)
omit [FiniteDimensional ℝ E] [CompactSpace M]

/-- Restriction of the actual fresh cutoff to the literal closed live set. -/
def liveCutoff (x : closure V) : ℝ := (s.cutoff * w) x.val

theorem liveCutoff_continuous
    (hw : Continuous w) : Continuous (s.liveCutoff h w W) :=
  (s.cutoff_smooth.continuous.mul hw).comp continuous_subtype_val

theorem liveCutoff_nonnegative (x : closure V) : 0 ≤ s.liveCutoff h w W x :=
  s.weight_nonnegative x.val

theorem liveCutoff_support :
    tsupport (s.liveCutoff h w W) ⊆ {x : closure V | x.val ∈ W} := by
  have hs : tsupport (s.liveCutoff h w W) ⊆
      (Subtype.val : closure V → M) ⁻¹' tsupport (s.cutoff * w) := by
    apply closure_minimal ?_ ((isClosed_tsupport _).preimage continuous_subtype_val)
    intro x hx
    exact subset_tsupport (s.cutoff * w) hx
  exact fun _ hx => s.weight_support (hs hx)

theorem liveCutoff_agreement (x : closure V) (hx : x.val ∈ closure s.retained) :
    s.liveCutoff h w W x = w x.val := s.weight_agreement hx

theorem retained_live : closure s.retained ⊆ W :=
  s.retained_collar.trans (subset_closure.trans s.collar_live)

theorem core_live : isolatedCore T (closure V) ⊆ s.retained := by
  rw [← h.actual_isolated_core]
  exact s.core_retained

end Data
end ConditionedStochasticStabilityHyperbolic.Paper.AdaptedLocalWeightSetup
