module

public import ConditionedStochasticStabilityHyperbolic.Paper.AdaptedLocalWeightSupportedProduct
public import ConditionedStochasticStabilityHyperbolic.Neighborhoods.CompactAnalysisCollar

/-! Actual cutoff and retained geometry for an arbitrary compact live set,
including filtration layers without a regular-closed boundary assumption. -/

public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.CompactLocalWeightSetup
open LeanShared
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M}
  (h : HL (E := E) T g Λ V) (w : M → ℝ) (K : Set M)

structure Data where
  collar : Set M
  retained : Set M
  cutoff : M → ℝ
  collar_open : IsOpen collar
  core_collar : Λ ⊆ collar
  collar_live : closure collar ⊆ V
  positive : ∀ x ∈ closure collar, 0 < w x ∧ 0 < w (T.symm x)
  retained_open : IsOpen retained
  core_retained : Λ ⊆ retained
  retained_collar : closure retained ⊆ collar
  no_return : (T '' closure retained) ∩ forwardTrapped T K ⊆ retained
  cutoff_smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ cutoff
  cutoff_support : tsupport cutoff ⊆ collar
  weight_nonnegative : ∀ x, 0 ≤ (cutoff * w) x
  weight_support : tsupport (cutoff * w) ⊆ V
  weight_agreement : EqOn (cutoff * w) w (closure retained)
  core_agreement : EqOn (cutoff * w) g Λ
  fresh : HL (E := E) T (cutoff * w) Λ V
  regularity_eq : fresh.r = h.r
  hyperbolic_eq : fresh.basic.hyperbolic = h.basic.hyperbolic


def of_supported_product (hK : IsCompact K) (hVK : V ⊆ K)
    (hcore : isolatedCore T K = Λ)
    (hw : Continuous w)
    (agree : EqOn w g Λ)
    (smoothProduct : ∀ ζ : M → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ →
      tsupport ζ ⊆ V → FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (h.r - 1) (ζ * w)) : Data h w K :=
  Classical.choice (by
    have positive : ∀ x ∈ Λ, 0 < w x := by
      intro x hx
      rw [agree hx]
      exact h.weight_positive x hx
    obtain ⟨G, B, hG, coreG, GW, pos, hB, coreB, BG, noReturn⟩ :=
      exists_twoSided_positive_compact_collar T K V Λ hK h.basic.open_neighborhood
        h.compact_core h.nonempty_core h.basic.subset_neighborhood hVK hcore w hw positive
    obtain ⟨ζ, smooth, _, support, _, nonnegative, supportWeight, retained⟩ :=
      SmoothWeightCutoff.exists_weight_cutoff_of_local_nonnegative (E := E)
        (closure B) G isClosed_closure.isCompact hG BG w hw
        (fun x hx => (pos x (subset_closure hx)).1.le)
    have supported : tsupport (ζ * w) ⊆ V :=
      supportWeight.trans (subset_closure.trans GW)
    have coreAgree : EqOn (ζ * w) g Λ := fun x hx =>
      (retained (subset_closure (coreB hx))).trans (agree hx)
    let fresh : HL (E := E) T (ζ * w) Λ V := {
      r := h.r
      regularity_gt_one := h.regularity_gt_one
      map_regular := h.map_regular
      inverse_regular := h.inverse_regular
      basic := h.basic
      weight_regular := smoothProduct ζ smooth (support.trans (subset_closure.trans GW))
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
variable (s : Data h w K)
omit [FiniteDimensional ℝ E] [CompactSpace M]

/-- Restriction of the actual fresh cutoff to the literal closed live set. -/
def liveCutoff (x : K) : ℝ := (s.cutoff * w) x.val

theorem liveCutoff_continuous
    (hw : Continuous w) : Continuous (s.liveCutoff h w K) :=
  (s.cutoff_smooth.continuous.mul hw).comp continuous_subtype_val

theorem liveCutoff_nonnegative (x : K) : 0 ≤ s.liveCutoff h w K x :=
  s.weight_nonnegative x.val

theorem liveCutoff_support :
    tsupport (s.liveCutoff h w K) ⊆ {x : K | x.val ∈ V} := by
  have hs : tsupport (s.liveCutoff h w K) ⊆
      (Subtype.val : K → M) ⁻¹' tsupport (s.cutoff * w) := by
    apply closure_minimal ?_ ((isClosed_tsupport _).preimage continuous_subtype_val)
    intro x hx
    exact subset_tsupport (s.cutoff * w) hx
  exact fun _ hx => s.weight_support (hs hx)

theorem liveCutoff_agreement (x : K) (hx : x.val ∈ closure s.retained) :
    s.liveCutoff h w K x = w x.val := s.weight_agreement hx

theorem retained_live : closure s.retained ⊆ V :=
  s.retained_collar.trans (subset_closure.trans s.collar_live)

theorem core_live (hcore : isolatedCore T K = Λ) : isolatedCore T K ⊆ s.retained := by
  rw [hcore]
  exact s.core_retained

end Data
end ConditionedStochasticStabilityHyperbolic.Paper.CompactLocalWeightSetup
