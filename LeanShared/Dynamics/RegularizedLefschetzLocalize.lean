module
public import LeanShared.Dynamics.RegularizedLefschetzUniform

/-! Localization of the regularized chart integrand. A point where the chart integrand at
time `N m` does not vanish lies in the data region of the periodic chart chain at a
`T^(N m)`-periodic point of the basic set in the marked chart set; data regions at distinct
periodic points are disjoint. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Bundle Metric MeasureTheory
open scoped Manifold ContDiff Topology NNReal
open LeanShared.PeriodicChartConstants LeanShared.PeriodicChartChains
namespace LeanShared.HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {b : BasicData (E := E) T Λ V}

namespace TraceSetup

variable (s : TraceSetup b)

theorem iterate_block (N m : ℕ) (x : M) :
    ((T ^ N : M ≃ₜ M) : M → M)^[m] x = (T : M → M)^[N * m] x := by
  rw [DiffeomorphismIterates.coe_pow, ← Function.iterate_mul]

/-- Points where the regularized integrand does not vanish nearly close up. -/
theorem nonvanishing_facts (κ : E → ℝ) (n : ℕ) (i : s.charts.ι) (z : E)
    (hz : s.integrand κ n i z ≠ 0) (ε : ℝ) (support : ∀ v, ε < ‖v‖ → κ v = 0) :
    z ∈ (s.charts.chart i).target ∧
      (s.charts.chart i).symm z ∈ tsupport (s.cutoff i) ∧
      (∀ l < n, (T : M → M)^[l] ((s.charts.chart i).symm z) ∈ closure V) ∧
      (T : M → M)^[n] ((s.charts.chart i).symm z) ∈ (s.charts.chart i).source ∧
      ‖s.charts.chart i ((T : M → M)^[n] ((s.charts.chart i).symm z)) - z‖ ≤ ε := by
  simp only [integrand] at hz
  by_cases target : z ∈ (s.charts.chart i).target
  · rw [Set.indicator_of_mem target] at hz
    set x := (s.charts.chart i).symm z
    have c0 : s.cutoff i x ≠ 0 := fun h => hz (by rw [h, zero_mul, zero_mul])
    have g0 : weightProduct T s.weight n x ≠ 0 := fun h => hz (by rw [h, mul_zero, zero_mul])
    have k0 : Set.indicator (s.charts.chart i).source
        (fun y => κ (s.charts.chart i y - z)) ((T : M → M)^[n] x) ≠ 0 :=
      fun h => hz (by rw [h, mul_zero])
    have source : (T : M → M)^[n] x ∈ (s.charts.chart i).source := by
      by_contra hs
      exact k0 (Set.indicator_of_notMem hs _)
    rw [Set.indicator_of_mem source] at k0
    refine ⟨target, subset_tsupport _ c0, fun l hl => ?_, source, ?_⟩
    · apply s.weight_support
      intro hg
      apply g0
      simp only [weightProduct]
      exact Finset.prod_eq_zero (Finset.mem_range.mpr hl) hg
    · by_contra far
      push Not at far
      exact k0 (support _ far)
  · exact absurd (Set.indicator_of_notMem target _) hz

/-- Localization in a chain region. -/
theorem localize_in_chain (κ : E → ℝ) (N m : ℕ) (i : s.charts.ι) (z : E) (ε : ℝ)
    (support : ∀ v, ε < ‖v‖ → κ v = 0) (hz : s.integrand κ (N * m) i z ≠ 0)
    (lam δloc ε1 εm sε : ℝ) (hδlam : δloc ≤ lam) (hδmargin : δloc ≤ s.margin)
    (hεm : ε ≤ εm) (hεs : ε ≤ sε)
    (markedMargin : cthickening εm (s.charts.chart i '' s.charts.marked i) ⊆
      s.charts.chart i '' s.charts.domain i)
    (chartClose : ∀ y ∈ s.charts.chart i '' closure (s.charts.domain i),
      ∀ y' ∈ s.charts.chart i '' closure (s.charts.domain i), ‖y - y'‖ ≤ sε →
        dist ((s.charts.chart i).symm y) ((s.charts.chart i).symm y') < ε1)
    (shadow : ∀ x : M, (∀ l < N * m, (T : M → M)^[l] x ∈ closure V) →
      dist ((T : M → M)^[N * m] x) x < ε1 →
      ∃ p ∈ Λ, (T : M → M)^[N * m] p = p ∧
        ∀ l ≤ N * m, dist ((T : M → M)^[l] x) ((T : M → M)^[l] p) < δloc)
    (δD : ℝ≥0) (hδD : 0 < δD)
    (chainOf : ∀ p : Λ, ((T ^ N : M ≃ₜ M) : M → M)^[m] p.val = p.val → p.val ∈ s.charts.marked i →
      PeriodicChain s.frame s.charts ((T ^ N : M ≃ₜ M) : M → M) lam p m i)
    (small' : ∀ p hfix hmk, (chainOf p hfix hmk).chain.k + δD * 2 < 1)
    (chartFwd : ∀ c : s.charts.ι, ∀ u ∈ closure (s.charts.domain c),
      ∀ v ∈ closure (s.charts.domain c), dist u v < δloc →
      ∀ p hfix hmk, ‖s.charts.chart c u - s.charts.chart c v‖ ≤
        (chainOf p hfix hmk).chain.radius δD / (chainOf p hfix hmk).chain.bound) :
    ∃ (p : Λ) (hfix : ((T ^ N : M ≃ₜ M) : M → M)^[m] p.val = p.val)
      (hmk : p.val ∈ s.charts.marked i),
      z ∈ (chainOf p hfix hmk).affine ⁻¹'
        ((chainOf p hfix hmk).chain.toData δD hδD (small' p hfix hmk)).region := by
  obtain ⟨target, tsupp, inV, source, closing⟩ := s.nonvanishing_facts κ (N * m) i z hz ε support
  set x := (s.charts.chart i).symm z
  have xMarked : x ∈ s.charts.marked i := s.cutoff_margin i (self_subset_cthickening _ tsupp)
  have xSource : x ∈ (s.charts.chart i).source :=
    s.charts.closure_domain i (subset_closure (s.charts.marked_domain i xMarked))
  have zEq : s.charts.chart i x = z := (s.charts.chart i).right_inv target
  -- the orbit segment nearly closes up
  have nearClose : dist ((T : M → M)^[N * m] x) x < ε1 := by
    have inThick : s.charts.chart i ((T : M → M)^[N * m] x) ∈
        cthickening εm (s.charts.chart i '' s.charts.marked i) :=
      mem_cthickening_of_dist_le _ (s.charts.chart i x) εm _ ⟨x, xMarked, rfl⟩
        (by rw [dist_eq_norm, zEq]; exact closing.trans hεm)
    obtain ⟨y, hy, hyEq⟩ := markedMargin inThick
    have mem1 : s.charts.chart i ((T : M → M)^[N * m] x) ∈
        s.charts.chart i '' closure (s.charts.domain i) := ⟨y, subset_closure hy, hyEq⟩
    have mem2 : z ∈ s.charts.chart i '' closure (s.charts.domain i) :=
      ⟨x, subset_closure (s.charts.marked_domain i xMarked), zEq⟩
    have := chartClose _ mem1 z mem2 (closing.trans hεs)
    rwa [(s.charts.chart i).left_inv source] at this
  obtain ⟨p, pΛ, pfix, close⟩ := shadow x inV nearClose
  have hfix : ((T ^ N : M ≃ₜ M) : M → M)^[m] p = p := by rw [iterate_block]; exact pfix
  have pMarked : p ∈ s.charts.marked i := by
    apply s.cutoff_margin i
    apply mem_cthickening_of_dist_le p x s.margin _ tsupp
    have := close 0 (Nat.zero_le _)
    simp only [Function.iterate_zero, id] at this
    rw [dist_comm]
    linarith
  set pc := chainOf ⟨p, pΛ⟩ hfix pMarked
  refine ⟨⟨p, pΛ⟩, hfix, pMarked, ?_⟩
  have encode := pc.encode δD hδD (small' _ _ _) x (fun j hj => ?_)
  · rw [Set.mem_preimage, PeriodicChain.affine_apply, ← zEq]
    exact encode.1
  · -- block iterates stay in the coordinate balls
    have pointEq : (pc.point j).val = ((T ^ N : M ≃ₜ M) : M → M)^[j] p := pc.point_val j
    have blockClose : dist (((T ^ N : M ≃ₜ M) : M → M)^[j] x) (pc.point j).val < δloc := by
      rw [pointEq, iterate_block, iterate_block]
      exact close _ (Nat.mul_le_mul_left N hj)
    have inDomain : ((T ^ N : M ≃ₜ M) : M → M)^[j] x ∈ s.charts.domain (pc.σ j) :=
      pc.good j _ (blockClose.trans_le hδlam)
    have pointDomain : (pc.point j).val ∈ s.charts.domain (pc.σ j) :=
      pc.good j _ (by rw [dist_self]; exact lt_of_le_of_lt (le_refl 0) (by
        have := dist_nonneg.trans_lt blockClose
        linarith))
    refine ⟨s.charts.closure_domain _ (subset_closure inDomain), ?_⟩
    have chartBound := chartFwd (pc.σ j) _ (subset_closure inDomain) _ (subset_closure pointDomain)
      blockClose ⟨p, pΛ⟩ hfix pMarked
    rw [pc.a_eq j]
    calc ‖(pc.chain.L j).symm (s.charts.chart (pc.σ j) (((T ^ N : M ≃ₜ M) : M → M)^[j] x) -
          s.charts.chart (pc.σ j) (pc.point j).val)‖
        ≤ ‖(pc.chain.L j).symm.toContinuousLinearMap‖ *
            ‖s.charts.chart (pc.σ j) (((T ^ N : M ≃ₜ M) : M → M)^[j] x) -
              s.charts.chart (pc.σ j) (pc.point j).val‖ :=
          (pc.chain.L j).symm.toContinuousLinearMap.le_opNorm _
      _ ≤ pc.chain.bound * (pc.chain.radius δD / pc.chain.bound) :=
          mul_le_mul (pc.chain.L_inv_bound j) chartBound (norm_nonneg _) pc.chain.bound_pos.le
      _ = pc.chain.radius δD := by field_simp [pc.chain.bound_pos.ne']

/-- Points of a chain region shadow its periodic orbit at all times. -/
theorem region_shadow (N m : ℕ) (i : s.charts.ι) (lam : ℝ) {p : Λ}
    (pc : PeriodicChain s.frame s.charts ((T ^ N : M ≃ₜ M) : M → M) lam p m i)
    (δD : ℝ≥0) (hδD : 0 < δD) (small' : pc.chain.k + δD * 2 < 1) (z : E)
    (hz : z ∈ pc.affine ⁻¹' (pc.chain.toData δD hδD small').region) (δdis sb sc : ℝ)
    (iterClose : ∀ u v : M, dist u v < sb → ∀ l < N,
      dist ((T : M → M)^[l] u) ((T : M → M)^[l] v) < δdis / 2)
    (chartSymm : ∀ c : s.charts.ι, ∀ y ∈ s.charts.chart c '' closure (s.charts.domain c),
      ∀ y' ∈ s.charts.chart c '' closure (s.charts.domain c), ‖y - y'‖ ≤ sc →
        dist ((s.charts.chart c).symm y) ((s.charts.chart c).symm y') < sb)
    (hsc : pc.chain.bound * pc.chain.radius δD ≤ sc) :
    ∀ l < N * m, dist ((T : M → M)^[l] ((s.charts.chart i).symm z)) ((T : M → M)^[l] p.val) <
      δdis / 2 := by
  set d := pc.chain.toData δD hδD small'
  set w := pc.affine z
  have hw : w ∈ d.region := hz
  have decodeEq : pc.decode w = (s.charts.chart i).symm z := by
    simp only [w, PeriodicChain.decode, PeriodicChain.affine_apply,
      ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
  set x := (s.charts.chart i).symm z
  have hr := pc.chain.radius_pos δD hδD
  have block (j : ℕ) (hj : j ≤ m) :
      dist (((T ^ N : M ≃ₜ M) : M → M)^[j] x) (pc.point j).val < sb := by
    obtain ⟨source, value⟩ := pc.orbit_eq δD hδD small' w hw j hj
    rw [decodeEq] at source value
    have small_j : ‖d.orbit j w‖ ≤ pc.chain.radius δD := hw j (by rw [show d.period = m from pc.period_eq]; exact hj)
    have coordinate : pc.chain.a j + pc.chain.L j (d.orbit j w) =
        s.charts.chart (pc.σ j) (((T ^ N : M ≃ₜ M) : M → M)^[j] x) := by
      rw [value, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
    have inBall := pc.ball_of_radius δD j _ (by linarith)
    rw [coordinate] at inBall
    have mem1 := image_mono subset_closure (pc.inChart j _ inBall)
    have mem2 := image_mono subset_closure (pc.inChart j _ (mem_closedBall_self pc.chain.ρ_pos.le))
    have near : ‖s.charts.chart (pc.σ j) (((T ^ N : M ≃ₜ M) : M → M)^[j] x) - pc.chain.a j‖ ≤ sc := by
      rw [← coordinate, add_sub_cancel_left]
      calc ‖pc.chain.L j (d.orbit j w)‖ ≤ pc.chain.bound * ‖d.orbit j w‖ :=
            ((pc.chain.L j).toContinuousLinearMap.le_opNorm _).trans
              (mul_le_mul_of_nonneg_right (pc.chain.L_bound j) (norm_nonneg _))
        _ ≤ pc.chain.bound * pc.chain.radius δD :=
            mul_le_mul_of_nonneg_left small_j pc.chain.bound_pos.le
        _ ≤ sc := hsc
    have := chartSymm (pc.σ j) _ mem1 _ mem2 near
    rwa [(s.charts.chart (pc.σ j)).left_inv source, pc.a_eq j,
      (s.charts.chart (pc.σ j)).left_inv (pc.source_point j)] at this
  intro l hl
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, zero_mul] at hl; exact absurd hl (Nat.not_lt_zero _)
    · exact h
  have jlt : l / N < m := by
    rw [Nat.div_lt_iff_lt_mul hN]
    rwa [mul_comm]
  have decompose : l = N * (l / N) + l % N := (Nat.div_add_mod l N).symm
  have := iterClose _ _ (block (l / N) jlt.le) (l % N) (Nat.mod_lt _ hN)
  rw [pc.point_val, iterate_block, iterate_block, ← Function.iterate_add_apply,
    ← Function.iterate_add_apply, add_comm (l % N), ← decompose] at this
  exact this

/-- On a chain region the integrand is the local chart integrand. -/
theorem integrand_on_region (κ : E → ℝ) (N m : ℕ) (i : s.charts.ι) (lam : ℝ) {p : Λ}
    (pc : PeriodicChain s.frame s.charts ((T ^ N : M ≃ₜ M) : M → M) lam p m i)
    (δD : ℝ≥0) (hδD : 0 < δD) (small' : pc.chain.k + δD * 2 < 1) (z : E)
    (hz : z ∈ pc.affine ⁻¹' (pc.chain.toData δD hδD small').region) :
    s.integrand κ (N * m) i z =
      (s.cutoff i ((s.charts.chart i).symm z) *
        weightProduct T s.weight (N * m) ((s.charts.chart i).symm z)) *
        κ (s.charts.chart i (((T ^ N : M ≃ₜ M) : M → M)^[m] ((s.charts.chart i).symm z)) - z) := by
  set d := pc.chain.toData δD hδD small'
  set w := pc.affine z
  have hw : w ∈ d.region := hz
  have decodeEq : pc.decode w = (s.charts.chart i).symm z := by
    simp only [w, PeriodicChain.decode, PeriodicChain.affine_apply,
      ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
  have hr := pc.chain.radius_pos δD hδD
  have hw0 : ‖w‖ ≤ 2 * pc.chain.radius δD := by
    have := hw 0 (Nat.zero_le _)
    change ‖w‖ ≤ pc.chain.radius δD at this
    linarith
  have target : z ∈ (s.charts.chart i).target := by
    have mem := pc.chart_symm_mem 0 _ (pc.ball_of_radius δD 0 w hw0)
    rw [pc.σ_zero] at mem
    have eq : pc.chain.a 0 + pc.chain.L 0 w = z := by
      simp only [w, PeriodicChain.affine_apply, ContinuousLinearEquiv.apply_symm_apply,
        add_sub_cancel]
    rw [eq] at mem
    rw [← mem.2]
    exact (s.charts.chart i).map_source mem.1
  have last := (pc.orbit_eq δD hδD small' w hw m le_rfl).1
  have σm : pc.σ (m : ℤ) = i := by
    have := pc.periodic_σ 0
    rwa [zero_add, pc.σ_zero] at this
  rw [σm, decodeEq, iterate_block] at last
  simp only [integrand, Set.indicator_of_mem target, Set.indicator_of_mem last, iterate_block]

end TraceSetup
end LeanShared.HyperbolicBasicSet
