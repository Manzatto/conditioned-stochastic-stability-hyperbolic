module
public import LeanShared.Dynamics.PeriodicChartChains

/-! Dictionary between periodic chart chains and the manifold dynamics. For the local
periodic closing data of a periodic chart chain, a point `w` of its region decodes to
`x = φ_i⁻¹(a_0 + L_0 w)`, the data orbit is the normalized chart coordinate of the block
iterates `H^j x`, and the closing map is `L_0⁻¹(φ_i(H^m x) - φ_i x)`. Conversely, a point whose
block iterates stay in the coordinate balls encodes into the region. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff Topology NNReal
open LeanShared.HyperbolicBasicSet LeanShared.PeriodicChartConstants
namespace LeanShared.PeriodicChartChains

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}
  {a : IsometricFraming h} {F : ChartFamily E M} {H : M → M} {lam : ℝ} {p : Λ} {m : ℕ} {i : F.ι}

namespace PeriodicChain

variable (pc : PeriodicChain a F H lam p m i) (δ : ℝ≥0) (hδ : 0 < δ) (small : pc.chain.k + δ * 2 < 1)

/-- The decoding of data coordinates at the base point. -/
@[expose] def decode (w : EuclideanSpace ℝ (Fin a.unstableDimension) ×
    EuclideanSpace ℝ (Fin a.stableDimension)) : M :=
  (F.chart i).symm (pc.chain.a 0 + pc.chain.L 0 w)

theorem ball_of_radius (j : ℤ) (v : EuclideanSpace ℝ (Fin a.unstableDimension) ×
    EuclideanSpace ℝ (Fin a.stableDimension)) (hv : ‖v‖ ≤ 2 * pc.chain.radius δ) :
    pc.chain.a j + pc.chain.L j v ∈ closedBall (pc.chain.a j) pc.chain.ρ :=
  pc.chain.inside δ j v hv

theorem chart_symm_mem (j : ℤ) (y : E) (hy : y ∈ closedBall (pc.chain.a j) pc.chain.ρ) :
    (F.chart (pc.σ j)).symm y ∈ (F.chart (pc.σ j)).source ∧
      F.chart (pc.σ j) ((F.chart (pc.σ j)).symm y) = y := by
  obtain ⟨x, hx, rfl⟩ := pc.inChart j y hy
  have source : x ∈ (F.chart (pc.σ j)).source := F.closure_domain _ (subset_closure hx)
  rw [(F.chart (pc.σ j)).left_inv source]
  exact ⟨source, rfl⟩

/-- The data orbit is the normalized chart coordinate of the block iterates. -/
theorem orbit_eq (w : EuclideanSpace ℝ (Fin a.unstableDimension) ×
    EuclideanSpace ℝ (Fin a.stableDimension)) (hw : w ∈ (pc.chain.toData δ hδ small).region) :
    ∀ j ≤ m, H^[j] (pc.decode w) ∈ (F.chart (pc.σ j)).source ∧
      (pc.chain.toData δ hδ small).orbit j w =
        (pc.chain.L j).symm (F.chart (pc.σ j) (H^[j] (pc.decode w)) - pc.chain.a j) := by
  set d := pc.chain.toData δ hδ small
  have hr := pc.chain.radius_pos δ hδ
  have hperiod : d.period = m := pc.period_eq
  intro j
  induction j with
  | zero =>
    intro _
    have hw0 : ‖w‖ ≤ 2 * pc.chain.radius δ := by
      have := hw 0 (Nat.zero_le _)
      change ‖w‖ ≤ pc.chain.radius δ at this
      linarith
    have base := pc.chart_symm_mem 0 _ (pc.ball_of_radius δ 0 w hw0)
    rw [pc.σ_zero] at base
    refine ⟨by simpa only [Function.iterate_zero, id, Nat.cast_zero, pc.σ_zero, decode] using base.1, ?_⟩
    simp only [Function.iterate_zero, id, LocalPeriodicClosing.Data.orbit_zero]
    change w = (pc.chain.L ((0 : ℕ) : ℤ)).symm (F.chart (pc.σ ((0 : ℕ) : ℤ))
      ((F.chart i).symm (pc.chain.a 0 + pc.chain.L 0 w)) - pc.chain.a ((0 : ℕ) : ℤ))
    simp only [Nat.cast_zero, pc.σ_zero]
    rw [base.2, add_sub_cancel_left, ContinuousLinearEquiv.symm_apply_apply]
  | succ j ih =>
    intro hj
    obtain ⟨source, value⟩ := ih (by omega)
    have small_j : ‖d.orbit j w‖ ≤ 2 * pc.chain.radius δ := by
      have := hw j (by rw [hperiod]; omega)
      change ‖d.orbit j w‖ ≤ pc.chain.radius δ at this
      linarith
    have coordinate : pc.chain.a j + pc.chain.L j (d.orbit j w) = F.chart (pc.σ j) (H^[j] (pc.decode w)) := by
      rw [value, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
    have inBall := pc.ball_of_radius δ j _ small_j
    rw [coordinate] at inBall
    have mappedNext := pc.mapped j _ inBall
    rw [(F.chart (pc.σ j)).left_inv source] at mappedNext
    have nextSource : H^[j + 1] (pc.decode w) ∈ (F.chart (pc.σ (j + 1))).source := by
      rw [Function.iterate_succ_apply']
      exact F.closure_domain _ (subset_closure mappedNext)
    refine ⟨by exact_mod_cast nextSource, ?_⟩
    rw [LocalPeriodicClosing.Data.orbit_succ]
    change pc.chain.H δ j (d.orbit j w) = _
    rw [pc.chain.H_eq δ hδ j _ small_j]
    simp only [ChartChainClosing.Chain.centered]
    rw [coordinate, pc.h_eq j]
    simp only [(F.chart (pc.σ j)).left_inv source, Function.iterate_succ_apply']
    push_cast
    rfl

/-- The closing map in chart coordinates. -/
theorem closing_eq (w : EuclideanSpace ℝ (Fin a.unstableDimension) ×
    EuclideanSpace ℝ (Fin a.stableDimension)) (hw : w ∈ (pc.chain.toData δ hδ small).region) :
    (pc.chain.toData δ hδ small).closing w =
      (pc.chain.L 0).symm (F.chart i (H^[m] (pc.decode w)) - F.chart i (pc.decode w)) := by
  have hm : (pc.chain.toData δ hδ small).period = m := pc.period_eq
  have last := (pc.orbit_eq δ hδ small w hw m le_rfl).2
  have first := (pc.orbit_eq δ hδ small w hw 0 (Nat.zero_le _)).2
  simp only [Function.iterate_zero, id, LocalPeriodicClosing.Data.orbit_zero, Nat.cast_zero,
    pc.σ_zero] at first
  have σm : pc.σ (m : ℤ) = i := by
    have := pc.periodic_σ 0
    rwa [zero_add, pc.σ_zero] at this
  have Lm : pc.chain.L (m : ℤ) = pc.chain.L 0 := by
    have := pc.chain.periodic_L 0
    rwa [zero_add, pc.period_eq] at this
  have am : pc.chain.a (m : ℤ) = pc.chain.a 0 := by
    have := pc.chain.periodic_a 0
    rwa [zero_add, pc.period_eq] at this
  rw [σm, Lm, am] at last
  have eq1 : (pc.chain.toData δ hδ small).closing w =
      (pc.chain.toData δ hδ small).orbit m w - w := by
    simp only [LocalPeriodicClosing.Data.closing, hm]
  rw [eq1, last]
  set x := pc.decode w
  calc (pc.chain.L 0).symm (F.chart i (H^[m] x) - pc.chain.a 0) - w =
      (pc.chain.L 0).symm (F.chart i (H^[m] x) - pc.chain.a 0) -
        (pc.chain.L 0).symm (F.chart i x - pc.chain.a 0) := by
        congr 1
    _ = (pc.chain.L 0).symm (F.chart i (H^[m] x) - F.chart i x) := by
        rw [← map_sub]
        congr 1
        abel

/-- Encoding: block iterates in the coordinate balls give a point of the region. -/
theorem encode (x : M)
    (hx : ∀ j ≤ m, H^[j] x ∈ (F.chart (pc.σ j)).source ∧
      ‖(pc.chain.L j).symm (F.chart (pc.σ j) (H^[j] x) - pc.chain.a j)‖ ≤ pc.chain.radius δ) :
    (pc.chain.L 0).symm (F.chart i x - pc.chain.a 0) ∈ (pc.chain.toData δ hδ small).region ∧
      pc.decode ((pc.chain.L 0).symm (F.chart i x - pc.chain.a 0)) = x := by
  set d := pc.chain.toData δ hδ small
  set w := (pc.chain.L 0).symm (F.chart i x - pc.chain.a 0)
  have hr := pc.chain.radius_pos δ hδ
  have source0 : x ∈ (F.chart i).source := by
    have := (hx 0 (Nat.zero_le _)).1
    simpa only [Function.iterate_zero, id, Nat.cast_zero, pc.σ_zero] using this
  have values : ∀ j ≤ m, d.orbit j w =
      (pc.chain.L j).symm (F.chart (pc.σ j) (H^[j] x) - pc.chain.a j) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [LocalPeriodicClosing.Data.orbit_zero, Function.iterate_zero, id, Nat.cast_zero,
        pc.σ_zero, w]
    | succ j ih =>
      intro hj
      have value := ih (by omega)
      have small_j : ‖d.orbit j w‖ ≤ 2 * pc.chain.radius δ := by
        rw [value]
        have := (hx j (by omega)).2
        linarith
      have coordinate : pc.chain.a j + pc.chain.L j (d.orbit j w) = F.chart (pc.σ j) (H^[j] x) := by
        rw [value, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
      rw [LocalPeriodicClosing.Data.orbit_succ]
      change pc.chain.H δ j (d.orbit j w) = _
      rw [pc.chain.H_eq δ hδ j _ small_j]
      simp only [ChartChainClosing.Chain.centered]
      rw [coordinate, pc.h_eq j]
      simp only [(F.chart (pc.σ j)).left_inv (hx j (by omega)).1, Function.iterate_succ_apply']
      push_cast
      rfl
  refine ⟨fun j hj => ?_, ?_⟩
  · have hperiod : d.period = m := pc.period_eq
    rw [hperiod] at hj
    rw [values j hj]
    exact (hx j hj).2
  · simp only [decode, w, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
    exact (F.chart i).left_inv source0

end PeriodicChain
end LeanShared.PeriodicChartChains
