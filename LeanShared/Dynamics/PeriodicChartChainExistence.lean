module
public import LeanShared.Dynamics.PeriodicChartChains

/-! Existence of uniform periodic chart chains: one block length and one set of constants
for every periodic orbit of the block map in `Λ` and every marked chart at its base point. -/
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

set_option maxHeartbeats 1600000 in
theorem exists_periodic_chains (a : IsometricFraming h) (F : ChartFamily E M)
    (cover : Λ ⊆ ⋃ i, F.domain i)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    {r : ℝ} (hr : 1 < r) (regular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T) :
    ∃ N : ℕ, 0 < N ∧ ∃ lam ρ bound holderC α : ℝ, 0 < lam ∧ 0 < ρ ∧ 0 < bound ∧
      0 ≤ holderC ∧ 0 < α ∧ α < 1 ∧
      ∀ (p : Λ) (m : ℕ) (_ : 0 < m),
        ((T ^ N : M ≃ₜ M) : M → M)^[m] p.val = p.val →
        ∀ i, p.val ∈ F.marked i →
          ∃ c : PeriodicChain a F ((T ^ N : M ≃ₜ M) : M → M) lam p m i,
            c.chain.ρ = ρ ∧ c.chain.bound = bound ∧ c.chain.holderC = holderC ∧
            c.chain.α = α ∧ c.chain.k = (1 / 8 : ℝ≥0) := by
  classical
  let := F.fintype
  obtain ⟨N, hN, blocks⟩ := h.exists_actual_tangent_blocks forward inverse (1 / 8) (by norm_num)
  set H : M → M := ((T ^ N : M ≃ₜ M) : M → M) with hH
  set α : ℝ := min ((r - 1) / 2) (1 / 2)
  have hα : 0 < α := lt_min (by linarith) (by norm_num)
  have hα1 : α < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have lower : α + 1 < r := by
    have : α ≤ (r - 1) / 2 := min_le_left _ _
    linarith
  have Hreg : FractionalManifoldRegularity.Regular (E := E) (F := E) (α + 1) H := by
    rw [hH, DiffeomorphismIterates.coe_pow]
    exact regular.iterate_lower_one_add hα hα1 lower N hN
  have Hcont : Continuous H := (T ^ N).continuous
  have Hsmooth : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) H :=
    DiffeomorphismIterates.mdifferentiable_pow T forward N
  have maps : ∀ x ∈ Λ, H x ∈ Λ := by
    have one : MapsTo T Λ Λ := fun x hx => by
      rw [← h.invariant]
      exact mem_image_of_mem T hx
    intro x hx
    rw [hH, DiffeomorphismIterates.coe_pow]
    exact one.iterate N hx
  obtain ⟨holderC, hC0, holder⟩ := F.exists_holder hα hα1 H Hreg Hcont
  obtain ⟨lam, ρ, hlam, hρ, lebesgue, markedGood, margins⟩ := F.exists_margins H Hcont Λ h.compact cover
  obtain ⟨Bf, hBf, frameBounds⟩ := a.exists_uniform_bound
  have fwd (i : F.ι) := CompactRiemannianChartBounds.forward (F.chart i) (F.mem i)
    (closure (F.domain i)) isClosed_closure.isCompact (F.closure_domain i)
  have inv (i : F.ι) := CompactRiemannianChartBounds.inverse (F.chart i) (F.mem i)
    (closure (F.domain i)) isClosed_closure.isCompact (F.closure_domain i)
  choose Cf hCf boundF using fwd
  choose Ci hCi boundI using inv
  set bound : ℝ := Bf * (∑ i, (Cf i + Ci i)) + 1
  have hbound : 0 < bound := by
    have : 0 ≤ ∑ i, (Cf i + Ci i) :=
      Finset.sum_nonneg fun i _ => add_nonneg (hCf i).le (hCi i).le
    positivity
  have sumLe (i : F.ι) : Cf i + Ci i ≤ ∑ j, (Cf j + Ci j) :=
    Finset.single_le_sum (f := fun j => Cf j + Ci j)
      (fun j _ => add_nonneg (hCf j).le (hCi j).le) (Finset.mem_univ i)
  -- framed blocks as functions of the point
  have blockData : ∀ x : Λ, ∃ A : EuclideanSpace ℝ (Fin a.unstableDimension) ≃L[ℝ]
      EuclideanSpace ℝ (Fin a.unstableDimension),
      ∃ B : EuclideanSpace ℝ (Fin a.stableDimension) →L[ℝ] EuclideanSpace ℝ (Fin a.stableDimension),
      ‖A.symm.toContinuousLinearMap‖ ≤ 1 / 8 ∧ ‖B‖ ≤ 1 / 8 ∧
      (a.whole ⟨H x.val, maps x.val x.property⟩).symm.toContinuousLinearMap.comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x.val).comp (a.whole x).toContinuousLinearMap) =
        (A : _ →L[ℝ] _).prodMap B := by
    intro x
    obtain ⟨S, U, hS, hU, stableAction, unstableAction, _⟩ := blocks x.val x.property
    obtain ⟨A, B, hA, hB, equation⟩ := PeriodicChartDerivative.framed_blocks a H x
      ⟨H x.val, maps x.val x.property⟩ rfl S U stableAction unstableAction
    exact ⟨A, B, hA.trans hU, hB.trans hS, equation⟩
  choose Afun Bfun hAfun hBfun hABfun using blockData
  refine ⟨N, hN, lam, ρ, bound, holderC, α, hlam, hρ, hbound, hC0, hα, hα1, ?_⟩
  intro p m hm fixed i hp
  set q : ℤ → Λ := orbitPoint H maps p m
  have step (j : ℤ) : H (q j).val = (q (j + 1)).val := orbitPoint_step H maps p m hm fixed j
  have periodicQ (j : ℤ) : q (j + m) = q j := orbitPoint_periodic H maps p m j
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  -- chart selection
  have choice (x : Λ) : ∃ k : F.ι, x.val ∈ F.good lam k := lebesgue x.val x.property
  set σ : ℤ → F.ι := fun j => if j % m = 0 then i else Classical.choose (choice (q j))
  have periodicσ (j : ℤ) : σ (j + m) = σ j := by
    simp only [σ, Int.add_emod_right, periodicQ]
  have good (j : ℤ) : (q j).val ∈ F.good lam (σ j) := by
    by_cases hj : j % m = 0
    · have qj : q j = p := by
        apply Subtype.ext
        simp only [q, orbitPoint, hj, Int.toNat_zero, Function.iterate_zero, id]
      simp only [σ, hj, ↓reduceIte, qj]
      exact markedGood i hp
    · simp only [σ, hj, ↓reduceIte]
      exact Classical.choose_spec (choice (q j))
  have inside (j : ℤ) : (q j).val ∈ (F.chart (σ j)).source :=
    F.closure_domain _ (subset_closure (F.good_domain lam hlam _ (good j)))
  have goodNext (j : ℤ) : H (q j).val ∈ F.good lam (σ (j + 1)) := by
    rw [step j]
    exact good (j + 1)
  -- normalizations as a function of (chart, point)
  have inside0 : p.val ∈ (F.chart i).source :=
    F.closure_domain _ (subset_closure (F.marked_domain i hp))
  let Lfun : F.ι × Λ → (EuclideanSpace ℝ (Fin a.unstableDimension) ×
      EuclideanSpace ℝ (Fin a.stableDimension)) ≃L[ℝ] E := fun kx =>
    if hx : kx.2.val ∈ (F.chart kx.1).source then
      PeriodicChartDerivative.normalization a (F.chart kx.1) (F.mem kx.1) kx.2 hx
    else PeriodicChartDerivative.normalization a (F.chart i) (F.mem i) p inside0
  have Leq (j : ℤ) : Lfun (σ j, q j) =
      PeriodicChartDerivative.normalization a (F.chart (σ j)) (F.mem (σ j)) (q j) (inside j) := by
    simp only [Lfun, inside j, ↓reduceDIte]
  -- margins at every site
  have site (j : ℤ) := margins (σ j) (σ (j + 1)) (q j).val (good j) (goodNext j)
  set hfun : ℤ → E → E := fun j y => F.chart (σ (j + 1)) (H ((F.chart (σ j)).symm y)) with hhfun
  set afun : ℤ → E := fun j => F.chart (σ j) (q j).val with hafun
  have targetOf (j : ℤ) (y : E) (hy : y ∈ closedBall (afun j) ρ) : y ∈ (F.chart (σ j)).target := by
    obtain ⟨x, hx, rfl⟩ := (site j).1 hy
    exact (F.chart _).map_source (F.closure_domain _ (subset_closure hx))
  have sourceOf (j : ℤ) (y : E) (hy : y ∈ closedBall (afun j) ρ) :
      H ((F.chart (σ j)).symm y) ∈ (F.chart (σ (j + 1))).source :=
    F.closure_domain _ (subset_closure ((site j).2.1 y hy))
  have diffAt (j : ℤ) (y : E) (hy : y ∈ closedBall (afun j) ρ) : DifferentiableAt ℝ (hfun j) y :=
    (F.contDiffAt hα hα1 H Hreg (σ j) (σ (j + 1)) y (targetOf j y hy) (sourceOf j y hy)).differentiableAt
      (by norm_num)
  have center (j : ℤ) : afun j ∈ closedBall (afun j) ρ := mem_closedBall_self hρ.le
  have diagonal (j : ℤ) : (Lfun (σ (j + 1), q (j + 1))).symm.toContinuousLinearMap.comp
      ((fderiv ℝ (hfun j) (afun j)).comp (Lfun (σ j, q j)).toContinuousLinearMap) =
      (Afun (q j) : _ →L[ℝ] _).prodMap (Bfun (q j)) := by
    have ex := PeriodicChartDerivative.exact_derivative a H (q j) (q (j + 1)) (step j)
      (F.chart (σ j)) (F.chart (σ (j + 1))) (F.mem _) (F.mem _) (inside j) (inside (j + 1))
      (Hsmooth (q j).val)
    have mine := CenteredManifoldCoordinates.centered_hasFDerivAt (Lfun (σ j, q j))
      (Lfun (σ (j + 1), q (j + 1))) (afun j) (afun (j + 1)) (hfun j)
      (fderiv ℝ (hfun j) (afun j)) ((diffAt j _ (center j)).hasFDerivAt)
    rw [Leq j, Leq (j + 1)] at mine ⊢
    rw [mine.unique ex]
    have e : q (j + 1) = ⟨H (q j).val, maps _ (q j).property⟩ := Subtype.ext (step j).symm
    rw [e]
    exact hABfun (q j)
  have periodicH (j : ℤ) : hfun (j + m) = hfun j := by
    funext y
    simp only [hhfun, show j + (m : ℤ) + 1 = j + 1 + m by ring, periodicσ]
  have Lbounds (j : ℤ) := normalization_bounds a (F.chart (σ j)) (F.mem _) (q j) (inside j) Bf
    (Cf (σ j)) (Ci (σ j)) (frameBounds (q j))
    (boundF (σ j) (q j).val (subset_closure (F.good_domain lam hlam _ (good j))))
    (boundI (σ j) (q j).val (subset_closure (F.good_domain lam hlam _ (good j))))
  have Lle (j : ℤ) : Cf (σ j) * Bf ≤ bound ∧ Bf * Ci (σ j) ≤ bound := by
    have s := sumLe (σ j)
    have c1 := hCi (σ j)
    have c2 := hCf (σ j)
    constructor <;> nlinarith
  let chain : ChartChainClosing.Chain (EuclideanSpace ℝ (Fin a.unstableDimension))
      (EuclideanSpace ℝ (Fin a.stableDimension)) E := {
    period := m
    period_pos := hm
    h := hfun
    h' := fun j y => fderiv ℝ (hfun j) y
    a := afun
    L := fun j => Lfun (σ j, q j)
    A := fun j => Afun (q j)
    B := fun j => Bfun (q j)
    ρ := ρ
    ρ_pos := hρ
    bound := bound
    bound_pos := hbound
    holderC := holderC
    holderC_nonneg := hC0
    α := α
    α_pos := hα
    k := 1 / 8
    hyperbolicA := fun j => by
      have := hAfun (q j)
      simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using this
    hyperbolicB := fun j => by
      have := hBfun (q j)
      simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using this
    orbit := fun j => by
      simp only [hhfun, hafun]
      rw [(F.chart (σ j)).left_inv (inside j), step j]
    derivative := fun j y hy => (diffAt j y hy).hasFDerivAt
    diagonal := diagonal
    holder := fun j y hy => holder (σ j) (σ (j + 1)) y ((site j).2.2 hy) (afun j)
      ((site j).2.2 (center j))
    continuousOn := fun j y hy => (diffAt j y hy).continuousAt.continuousWithinAt
    L_bound := fun j => by
      rw [Leq j]
      exact (Lbounds j).1.trans (Lle j).1
    L_inv_bound := fun j => by
      rw [Leq j]
      exact (Lbounds j).2.trans (Lle j).2
    periodic_h := periodicH
    periodic_h' := fun j => by
      funext y
      rw [periodicH j]
    periodic_a := fun j => by simp only [hafun, periodicσ, periodicQ]
    periodic_L := fun j => by simp only [periodicσ, periodicQ]
    periodic_A := fun j => by simp only [periodicQ]
    periodic_B := fun j => by simp only [periodicQ] }
  have σzero : σ 0 = i := by simp only [σ, Int.zero_emod, ↓reduceIte]
  have framedEq (j : ℤ) : (Afun (q j) : EuclideanSpace ℝ (Fin a.unstableDimension) →L[ℝ] _).prodMap
      (Bfun (q j)) = (a.whole (q (j + 1))).symm.toContinuousLinearMap.comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H (q j).val).comp (a.whole (q j)).toContinuousLinearMap) := by
    have e : q (j + 1) = ⟨H (q j).val, maps _ (q j).property⟩ := Subtype.ext (step j).symm
    rw [e]
    exact (hABfun (q j)).symm
  exact ⟨PeriodicChain.mk chain σ q rfl σzero (orbitPoint_zero H maps p m) step periodicσ periodicQ
    (fun j => rfl) (fun j => rfl) good inside (fun j y hy => (site j).1 hy)
    (fun j y hy => (site j).2.1 y hy) framedEq, rfl, rfl, rfl, rfl, rfl⟩

end LeanShared.PeriodicChartChains
