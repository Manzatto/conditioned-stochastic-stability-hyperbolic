module
public import LeanShared.Geometry.BoundedRiemannianInverseChartLipschitz
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! For every chart of the maximal atlas, the inverse chart is Lipschitz on
each compact subset of its target, for the constructed bounded Riemannian
length metric: locally it is the inverse standard chart (locally Lipschitz)
composed with the smooth chart transition, and a Lebesgue number together
with the boundedness of the compact manifold gives one global constant. -/
public noncomputable section
set_option linter.unusedSectionVars false
namespace LeanShared.BoundedRiemannianMetric
open Set Manifold Metric Bundle Filter IsManifold
open scoped Topology Manifold ContDiff Bundle NNReal

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

set_option maxHeartbeats 1600000 in
theorem inverse_chart_local (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (y : E) (hy : y ∈ c.target) :
    let _ : MetricSpace M := metric (E := E)
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ L : ℝ≥0, ball y ρ ⊆ c.target ∧
      ∀ z ∈ ball y ρ, ∀ w ∈ ball y ρ, dist (c.symm z) (c.symm w) ≤ L * dist z w := by
  intro _
  let x := c.symm y
  have hx : x ∈ c.source := c.map_target hy
  obtain ⟨r, hr, C, _, _, lip⟩ := inverse_chart_local_lipschitz (E := E) (M := M) x
  let τ : E → E := fun z => extChartAt (𝓘(ℝ,E)) x (c.symm z)
  have symmAt : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ c.symm y :=
    (contMDiffOn_symm_of_mem_maximalAtlas hc).contMDiffAt (c.open_target.mem_nhds hy)
  have extAt : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (extChartAt (𝓘(ℝ,E)) x) (c.symm y) :=
    (contMDiffOn_extChartAt (n := ∞)).contMDiffAt
      ((chartAt E x).open_source.mem_nhds (mem_chart_source E x))
  have hτ : ContDiffAt ℝ 1 τ y := by
    have comp := extAt.comp y symmAt
    rw [contMDiffAt_iff_contDiffAt] at comp
    exact comp.of_le (by norm_num)
  obtain ⟨K, t, ht, lipτ⟩ := hτ.exists_lipschitzOnWith
  have τy : τ y = extChartAt (𝓘(ℝ,E)) x x := rfl
  have nearSource : c.symm ⁻¹' (extChartAt (𝓘(ℝ,E)) x).source ∈ 𝓝 y :=
    (c.continuousAt_symm hy).preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) x).mem_nhds (mem_extChartAt_source x))
  have nearBall : τ ⁻¹' ball (extChartAt (𝓘(ℝ,E)) x x) r ∈ 𝓝 y :=
    hτ.continuousAt.preimage_mem_nhds (by rw [τy]; exact ball_mem_nhds _ hr)
  have all : t ∩ c.target ∩ c.symm ⁻¹' (extChartAt (𝓘(ℝ,E)) x).source ∩
      τ ⁻¹' ball (extChartAt (𝓘(ℝ,E)) x x) r ∈ 𝓝 y :=
    inter_mem (inter_mem (inter_mem ht (c.open_target.mem_nhds hy)) nearSource) nearBall
  obtain ⟨ρ, hρ, sub⟩ := Metric.mem_nhds_iff.mp all
  refine ⟨ρ, hρ, C * K, fun z hz => (sub hz).1.1.2, ?_⟩
  intro z hz w hw
  have hz' := sub hz
  have hw' := sub hw
  have ez : (extChartAt (𝓘(ℝ,E)) x).symm (τ z) = c.symm z :=
    (extChartAt (𝓘(ℝ,E)) x).left_inv hz'.1.2
  have ew : (extChartAt (𝓘(ℝ,E)) x).symm (τ w) = c.symm w :=
    (extChartAt (𝓘(ℝ,E)) x).left_inv hw'.1.2
  have step1 := lip (τ z) hz'.2 (τ w) hw'.2
  rw [ez, ew] at step1
  have step2 : dist (τ z) (τ w) ≤ K * dist z w := lipτ.dist_le_mul z hz'.1.1.1 w hw'.1.1.1
  calc dist (c.symm z) (c.symm w) ≤ C * dist (τ z) (τ w) := step1
    _ ≤ C * (K * dist z w) := mul_le_mul_of_nonneg_left step2 (by positivity)
    _ = ↑(C * K) * dist z w := by push_cast; ring

/-- The inverse chart is Lipschitz on every compact subset of the chart target. -/
theorem inverse_chart_compact (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (K : Set E) (compact : IsCompact K)
    (inside : K ⊆ c.target) :
    let _ : MetricSpace M := metric (E := E)
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z ∈ K, ∀ w ∈ K, dist (c.symm z) (c.symm w) ≤ L * dist z w := by
  let _ : MetricSpace M := metric (E := E)
  rcases K.eq_empty_or_nonempty with empty | ⟨k, hk⟩
  · exact ⟨0, le_rfl, fun z hz => by rw [empty] at hz; exact hz.elim⟩
  let base : M := c.symm k
  choose ρ hρ L _ localBound using fun y : K => inverse_chart_local (E := E) (M := M) c hc y (inside y.2)
  -- finitely many half balls cover `K`
  obtain ⟨cover, hcover⟩ := compact.elim_finite_subcover (fun y : K => ball (y : E) (ρ y / 2))
    (fun _ => isOpen_ball)
    (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (half_pos (hρ ⟨z, hz⟩))⟩)
  -- a Lebesgue number for that finite cover
  obtain ⟨δ, hδ, lebesgue⟩ := lebesgue_number_lemma_of_metric compact
    (c := fun y : cover => ball ((y : K) : E) (ρ y / 2)) (fun _ => isOpen_ball)
    (fun z hz => by
      obtain ⟨y, hy, mem⟩ := mem_iUnion₂.mp (hcover hz)
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, mem⟩)
  -- the compact manifold is bounded
  obtain ⟨D, hD⟩ := (isCompact_univ (X := M)).isBounded.subset_closedBall base
  have hD0 : 0 ≤ D := le_trans dist_nonneg (hD (mem_univ base))
  let L₀ : ℝ≥0 := cover.sup L
  refine ⟨max (L₀ : ℝ) (2 * D / δ), le_max_of_le_left L₀.2, ?_⟩
  intro z hz w hw
  by_cases near : dist z w < δ
  · obtain ⟨y, hy⟩ := lebesgue z hz
    have hzy : z ∈ ball ((y : K) : E) (ρ y) :=
      ball_subset_ball (half_le_self (hρ y).le) (hy (mem_ball_self hδ))
    have hwy : w ∈ ball ((y : K) : E) (ρ y) :=
      ball_subset_ball (half_le_self (hρ y).le) (hy (by rw [mem_ball, dist_comm]; exact near))
    have hL : (L y : ℝ) ≤ L₀ := by
      exact_mod_cast Finset.le_sup (f := L) y.2
    calc dist (c.symm z) (c.symm w) ≤ L y * dist z w := localBound y z hzy w hwy
      _ ≤ max (L₀ : ℝ) (2 * D / δ) * dist z w :=
        mul_le_mul_of_nonneg_right (hL.trans (le_max_left _ _)) dist_nonneg
  · push Not at near
    have far : dist (c.symm z) (c.symm w) ≤ 2 * D := by
      have h1 := hD (mem_univ (c.symm z))
      have h2 := hD (mem_univ (c.symm w))
      rw [mem_closedBall] at h1 h2
      calc dist (c.symm z) (c.symm w) ≤ dist (c.symm z) base +
            dist (c.symm w) base := dist_triangle_right _ _ _
        _ ≤ D + D := add_le_add h1 h2
        _ = 2 * D := by ring
    calc dist (c.symm z) (c.symm w) ≤ 2 * D := far
      _ = 2 * D / δ * δ := by field_simp
      _ ≤ 2 * D / δ * dist z w :=
        mul_le_mul_of_nonneg_left near (div_nonneg (by linarith) hδ.le)
      _ ≤ max (L₀ : ℝ) (2 * D / δ) * dist z w :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg

end LeanShared.BoundedRiemannianMetric
