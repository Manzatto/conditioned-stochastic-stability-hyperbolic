module
public import LeanShared.Dynamics.PeriodicChartConstants

/-! Uniform margins for chart chains. For a finite chart family whose domains cover a
compact set `Λ`, there are `λ > 0` and `ρ > 0` such that every point of `Λ` has its
`λ`-ball inside some domain, every marked point has its `λ`-ball inside its own domain,
and whenever `x` and `H x` have their `λ`-balls inside the domains of charts `i` and `j`,
the closed `ρ`-ball around `φ_i x` lies in `φ_i(D_i)`, is mapped by `H ∘ φ_i⁻¹` into `D_j`,
and lies in the compact piece of the pair `(i, j)`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff Topology
namespace LeanShared.PeriodicChartConstants

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

theorem exists_uniform_lower {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ f i := by
  classical
  by_cases h : Nonempty ι
  · obtain ⟨i0, _, hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
    exact ⟨f i0, hf i0, fun i => hmin i (Finset.mem_univ i)⟩
  · exact ⟨1, one_pos, fun i => (h ⟨i⟩).elim⟩

namespace ChartFamily

variable (F : ChartFamily E M)

/-- Points whose `λ`-ball lies in the domain of chart `i`. -/
@[expose] def good (lam : ℝ) (i : F.ι) : Set M := {x | ∀ y, dist y x < lam → y ∈ F.domain i}

theorem good_eq (lam : ℝ) (i : F.ι) : F.good lam i = (thickening lam (F.domain i)ᶜ)ᶜ := by
  ext x
  simp only [good, mem_compl_iff, mem_thickening_iff, not_exists, not_and]
  constructor
  · intro h y hy close
    exact hy (h y (by rw [dist_comm]; exact close))
  · intro h y close
    by_contra hy
    exact h y hy (by rw [dist_comm]; exact close)

theorem isClosed_good (lam : ℝ) (i : F.ι) : IsClosed (F.good lam i) := by
  rw [good_eq]
  exact isOpen_thickening.isClosed_compl

theorem good_domain (lam : ℝ) (hlam : 0 < lam) (i : F.ι) : F.good lam i ⊆ F.domain i :=
  fun x hx => hx x (by rw [dist_self]; exact hlam)

/-- Uniform margins. -/
theorem exists_margins (H : M → M) (hH : Continuous H) (Λ : Set M) (compactΛ : IsCompact Λ)
    (cover : Λ ⊆ ⋃ i, F.domain i) :
    ∃ lam ρ : ℝ, 0 < lam ∧ 0 < ρ ∧
      (∀ x ∈ Λ, ∃ i, x ∈ F.good lam i) ∧
      (∀ i, F.marked i ⊆ F.good lam i) ∧
      ∀ i j (x : M), x ∈ F.good lam i → H x ∈ F.good lam j →
        closedBall (F.chart i x) ρ ⊆ F.chart i '' F.domain i ∧
        (∀ y ∈ closedBall (F.chart i x) ρ, H ((F.chart i).symm y) ∈ F.domain j) ∧
        closedBall (F.chart i x) ρ ⊆ F.piece H i j := by
  let := F.fintype
  -- Lebesgue number on Λ
  obtain ⟨lam0, hlam0, lebesgue⟩ := lebesgue_number_lemma_of_metric compactΛ
    (fun i => F.isOpen_domain i) cover
  -- marked margins
  have marked (i : F.ι) : ∃ μ : ℝ, 0 < μ ∧ thickening μ (F.marked i) ⊆ F.domain i :=
    (F.compact_marked i).exists_thickening_subset_open (F.isOpen_domain i) (F.marked_domain i)
  choose μ hμ hμsub using marked
  obtain ⟨μ0, hμ0, hμle⟩ := exists_uniform_lower μ hμ
  set lam := min lam0 μ0
  have hlam : 0 < lam := lt_min hlam0 hμ0
  -- chart thickenings of the good sets
  have chartMargin (i : F.ι) : ∃ ρ : ℝ, 0 < ρ ∧
      cthickening ρ (F.chart i '' F.good lam i) ⊆ F.chart i '' F.domain i := by
    have compact : IsCompact (F.chart i '' F.good lam i) :=
      (F.isClosed_good lam i).isCompact.image_of_continuousOn
        ((F.chart i).continuousOn.mono ((F.good_domain lam hlam i).trans
          (subset_closure.trans (F.closure_domain i))))
    have openImage : IsOpen (F.chart i '' F.domain i) :=
      (F.chart i).isOpen_image_of_subset_source (F.isOpen_domain i)
        (subset_closure.trans (F.closure_domain i))
    exact compact.exists_cthickening_subset_open openImage
      (image_mono (F.good_domain lam hlam i))
  choose ρ1 hρ1 hρ1sub using chartMargin
  -- uniform continuity of H ∘ φ_i⁻¹ on the compact chart images
  have uniform (i : F.ι) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ F.chart i '' closure (F.domain i),
      ∀ z ∈ F.chart i '' closure (F.domain i), dist y z < ρ →
        dist (H ((F.chart i).symm y)) (H ((F.chart i).symm z)) < lam := by
    have continuous : ContinuousOn (fun y => H ((F.chart i).symm y))
        (F.chart i '' closure (F.domain i)) :=
      hH.comp_continuousOn ((F.chart i).continuousOn_symm.mono (F.image_target i))
    have uc := (F.compact_image i).uniformContinuousOn_of_continuous continuous
    rw [Metric.uniformContinuousOn_iff] at uc
    obtain ⟨ρ, hρ, h⟩ := uc lam hlam
    exact ⟨ρ, hρ, fun y hy z hz close => h y hy z hz close⟩
  choose ρ2 hρ2 hρ2close using uniform
  obtain ⟨ρ1', hρ1', hρ1le⟩ := exists_uniform_lower ρ1 hρ1
  obtain ⟨ρ2', hρ2', hρ2le⟩ := exists_uniform_lower ρ2 hρ2
  set ρ := min ρ1' (ρ2' / 2)
  have hρ : 0 < ρ := lt_min hρ1' (by positivity)
  refine ⟨lam, ρ, hlam, hρ, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := lebesgue x hx
    exact ⟨i, fun y close => hi (mem_ball.mpr (close.trans_le (min_le_left _ _)))⟩
  · intro i x hx y close
    apply hμsub i
    exact mem_thickening_iff.mpr ⟨x, hx, close.trans_le ((min_le_right _ _).trans (hμle i))⟩
  · intro i j x hx hHx
    have inChart : closedBall (F.chart i x) ρ ⊆ F.chart i '' F.domain i := by
      intro y hy
      apply hρ1sub i
      apply mem_cthickening_of_dist_le y (F.chart i x) (ρ1 i) (F.chart i '' F.good lam i) ⟨x, hx, rfl⟩
      exact (mem_closedBall.mp hy).trans ((min_le_left _ _).trans (hρ1le i))
    have closureImage : F.chart i '' F.domain i ⊆ F.chart i '' closure (F.domain i) :=
      image_mono subset_closure
    have xSource : x ∈ (F.chart i).source :=
      F.closure_domain i (subset_closure (F.good_domain lam hlam i hx))
    have mapped : ∀ y ∈ closedBall (F.chart i x) ρ, H ((F.chart i).symm y) ∈ F.domain j := by
      intro y hy
      apply hHx
      have close := hρ2close i y (closureImage (inChart hy)) (F.chart i x)
        (closureImage ⟨x, F.good_domain lam hlam i hx, rfl⟩)
        (by
          have : dist y (F.chart i x) ≤ ρ := mem_closedBall.mp hy
          have : ρ ≤ ρ2' / 2 := min_le_right _ _
          have : ρ2' ≤ ρ2 i := hρ2le i
          linarith)
      rwa [(F.chart i).left_inv xSource] at close
    refine ⟨inChart, mapped, fun y hy => ⟨closureImage (inChart hy), subset_closure (mapped y hy)⟩⟩

end ChartFamily
end LeanShared.PeriodicChartConstants
