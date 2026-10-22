module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseFiniteWords
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseValidItinerary
public import LeanShared.Analysis.PointwiseJetCoordinates
public import LeanShared.Analysis.ChartReexpressionGerm
import all LeanShared.Analysis.FiniteJetComposition

/-! Actual inverse words converge in C¹ in arbitrary fixed smooth chart pairs.
The inverse itinerary is constructed from the original atlas; no inverse
Whitney bound or convergence rate is assumed. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal
open LeanShared.FiniteJetComposition

set_option maxHeartbeats 2400000 in
theorem InverseFamily.actual_word_jets_in_charts
    {E M ι A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (ε : A → ℝ≥0) (controls : ℕ → ∀ a, cube (ι := ι) (ε a)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ a in l, 0 < ε a)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (N : ℕ) :
    JetConvergesOn
      (fun a => d ∘ word (fun n => fun y => J.map (ε a) ((controls n a).val,y)) N ∘ c.symm)
      (d ∘ (T.symm : M → M)^[N] ∘ c.symm) l
      (c.target ∩ ((T.symm : M → M)^[N] ∘ c.symm) ⁻¹' d.source) := by
  intro y hy
  let x := c.symm y
  have cover (n : ℕ) : ∃ i, (T.symm : M → M)^[n] x ∈ J.atlas.patch i := by
    have inside : (T.symm : M → M)^[n] x ∈ ⋃ i, J.atlas.patch i :=
      J.atlas.patch_cover.symm ▸ mem_univ _
    exact mem_iUnion.mp inside
  choose chart patches using cover
  let s := J.atlas.source (chart 0)
  let t := J.atlas.source (chart N)
  have sources (n : ℕ) : (T.symm : M → M)^[n] x ∈ (J.atlas.source (chart n)).source :=
    J.atlas.patch_source (chart n) (subset_closure (patches n))
  have hs : x ∈ s.source := sources 0
  have ht : (T.symm : M → M)^[N] x ∈ t.source := sources N
  have inside := J.atlas.mem_actualWordDomain_of_patch_itinerary chart x patches N
  have jets := J.actual_word_jets regularity deterministic inverse ε controls l limit positive chart N
  have first : ContDiffAt ℝ 1 (s ∘ c.symm) y := by
    have a : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 c.symm y :=
      (contMDiffAt_symm_of_mem_maximalAtlas hc hy.1).of_le (by simp)
    have b : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 s (c.symm y) :=
      (contMDiffAt_of_mem_maximalAtlas (J.atlas.source_smooth (chart 0)) hs).of_le (by simp)
    exact (b.comp y a).contDiffAt
  have endpoint : (s.symm (s (c.symm y))) = x := s.left_inv hs
  have last : ContDiffAt ℝ 1 (d ∘ t.symm)
      ((t ∘ (T.symm : M → M)^[N] ∘ s.symm) ((s ∘ c.symm) y)) := by
    simp only [Function.comp_apply, endpoint]
    have a : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 t.symm (t ((T.symm : M → M)^[N] x)) :=
      (contMDiffAt_symm_of_mem_maximalAtlas (J.atlas.source_smooth (chart N))
        (t.map_source ht)).of_le (by simp)
    have b : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 d ((T.symm : M → M)^[N] x) :=
      (contMDiffAt_of_mem_maximalAtlas hd hy.2).of_le (by simp)
    have b' : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 d
        (t.symm (t ((T.symm : M → M)^[N] x))) := by
      rw [t.left_inv ht]
      exact b
    exact (b'.comp _ a).contDiffAt
  have transformed := jets.fixed_coordinates_at (s ∘ c.symm) (d ∘ t.symm) y inside first last
  have finalJets := transformed.congr_moving_germs
    (g₀ := d ∘ (T.symm : M → M)^[N] ∘ c.symm)
    (g := fun a => d ∘ word (fun n => fun y => J.map (ε a) ((controls n a).val,y)) N ∘ c.symm)
    (by
      intro z hz
      have same : z = y := mem_singleton_iff.mp hz
      subst z
      exact LeanShared.chart_reexpression_germ c d s t ((T.symm : M → M)^[N])
        (T.symm.continuous.iterate N) y hy.1 hs ht)
    (by
      intro z hz v moving
      have same : z = y := mem_singleton_iff.mp hz
      subst z
      have input := (c.continuousAt_symm hy.1).tendsto.comp moving
      have nearFirst := input.eventually (s.open_source.mem_nhds hs)
      have nearLast := (J.moving_word_tendsto ε controls l limit positive _ _ input N).eventually
        (t.open_source.mem_nhds ht)
      have nearInitial := moving.eventually (c.open_target.mem_nhds hy.1)
      have window : ∀ᶠ a in l, ε a ≤ J.window :=
        (limit.eventually (gt_mem_nhds J.positive)).mono (fun _ h => h.le)
      filter_upwards [nearFirst, nearLast, nearInitial, positive, window] with a ha hb hi hp hw
      exact LeanShared.chart_reexpression_germ c d s t _
        (word_continuous _ (fun n =>
          (J.map_contMDiff (ε a) hp hw (controls n a)).continuous) N)
        (v a) hi ha hb)
  exact finalJets y (mem_singleton y)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
