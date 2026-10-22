module
public import LeanShared.Dynamics.PeriodicChartMargins
public import LeanShared.Dynamics.ChartChainClosing
public import LeanShared.Geometry.DiffeomorphismIterates

/-! Uniform chart chains along periodic orbits of a hyperbolic set. For a `C^r` (`r > 1`)
diffeomorphism with hyperbolic set `Λ`, Euclidean splitting frames and a finite chart family
covering `Λ`, one block length `N` and one set of constants serve every periodic orbit of
`T^N` in `Λ` and every marked chart at its base point: the chart representatives of `T^N`
along the orbit, normalized by chart differentials and frames, form a
`ChartChainClosing.Chain` whose first chart is the given marked chart. -/
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

/-- A periodic chart chain at a periodic point with a prescribed first chart. -/
structure PeriodicChain (a : IsometricFraming h) (F : ChartFamily E M) (H : M → M)
    (lam : ℝ) (p : Λ) (m : ℕ) (i : F.ι) where
  chain : ChartChainClosing.Chain (EuclideanSpace ℝ (Fin a.unstableDimension))
    (EuclideanSpace ℝ (Fin a.stableDimension)) E
  σ : ℤ → F.ι
  point : ℤ → Λ
  period_eq : chain.period = m
  σ_zero : σ 0 = i
  point_zero : point 0 = p
  point_step : ∀ j, H (point j).val = (point (j + 1)).val
  periodic_σ : ∀ j, σ (j + m) = σ j
  periodic_point : ∀ j, point (j + m) = point j
  h_eq : ∀ j, chain.h j = fun y => F.chart (σ (j + 1)) (H ((F.chart (σ j)).symm y))
  a_eq : ∀ j, chain.a j = F.chart (σ j) (point j).val
  good : ∀ j, (point j).val ∈ F.good lam (σ j)
  source_point : ∀ j, (point j).val ∈ (F.chart (σ j)).source
  inChart : ∀ j y, y ∈ closedBall (chain.a j) chain.ρ → y ∈ F.chart (σ j) '' F.domain (σ j)
  mapped : ∀ j y, y ∈ closedBall (chain.a j) chain.ρ →
    H ((F.chart (σ j)).symm y) ∈ F.domain (σ (j + 1))
  framed : ∀ j, (chain.A j : EuclideanSpace ℝ (Fin a.unstableDimension) →L[ℝ] _).prodMap (chain.B j) =
    (a.whole (point (j + 1))).symm.toContinuousLinearMap.comp
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H (point j).val).comp (a.whole (point j)).toContinuousLinearMap)

/-- Periodic orbit points indexed by `ℤ`. -/
@[expose] def orbitPoint (H : M → M) (maps : ∀ x ∈ Λ, H x ∈ Λ) (p : Λ) (m : ℕ) (j : ℤ) : Λ :=
  ⟨H^[(j % m).toNat] p.val, by
    have all : ∀ n : ℕ, H^[n] p.val ∈ Λ := by
      intro n
      induction n with
      | zero => exact p.property
      | succ n ih => rw [Function.iterate_succ_apply']; exact maps _ ih
    exact all _⟩

theorem orbitPoint_step (H : M → M) (maps : ∀ x ∈ Λ, H x ∈ Λ) (p : Λ) (m : ℕ) (hm : 0 < m)
    (fixed : H^[m] p.val = p.val) (j : ℤ) :
    H (orbitPoint H maps p m j).val = (orbitPoint H maps p m (j + 1)).val := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have r0 := Int.emod_nonneg j hm'.ne'
  have r1 := Int.emod_lt_of_pos j hm'
  have decomposition := Int.emod_add_mul_ediv j m
  simp only [orbitPoint]
  rw [show H (H^[(j % m).toNat] p.val) = H^[(j % m).toNat + 1] p.val from
    (Function.iterate_succ_apply' H _ _).symm]
  rcases lt_or_eq_of_le (show j % m + 1 ≤ m by omega) with lt | eq
  · have next : (j + 1) % m = j % m + 1 := by
      rw [show j + 1 = (j % m + 1) + m * (j / m) by omega, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by omega) lt]
    rw [next, show (j % m + 1).toNat = (j % m).toNat + 1 by omega]
  · have next : (j + 1) % m = 0 := by
      rw [show j + 1 = m * (j / m + 1) by rw [mul_add, mul_one]; omega]
      exact Int.mul_emod_right _ _
    rw [next, show (j % m).toNat + 1 = m by omega]
    simpa only [Int.toNat_zero, Function.iterate_zero, id] using fixed

theorem orbitPoint_periodic (H : M → M) (maps : ∀ x ∈ Λ, H x ∈ Λ) (p : Λ) (m : ℕ) (j : ℤ) :
    orbitPoint H maps p m (j + m) = orbitPoint H maps p m j := by
  simp only [orbitPoint, Int.add_emod_right]

theorem orbitPoint_zero (H : M → M) (maps : ∀ x ∈ Λ, H x ∈ Λ) (p : Λ) (m : ℕ) :
    orbitPoint H maps p m 0 = p := by
  apply Subtype.ext
  simp only [orbitPoint, Int.zero_emod, Int.toNat_zero, Function.iterate_zero, id]

/-- Norm bounds of chart normalizations. -/
theorem normalization_bounds (a : IsometricFraming h) (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (x : Λ) (inside : x.val ∈ c.source)
    (Bf Cf Ci : ℝ) (frame : ‖(a.whole x).toContinuousLinearMap‖ ≤ Bf ∧
      ‖(a.whole x).symm.toContinuousLinearMap‖ ≤ Bf)
    (forward : ‖(NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x.val)).toContinuousLinearMap.comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) c x.val)‖ ≤ Cf)
    (inverse : ‖((CompactRiemannianChartBounds.chart_differentiable c hc).mfderiv inside).symm.toContinuousLinearMap.comp
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x.val)).symm.toContinuousLinearMap‖ ≤ Ci) :
    ‖(PeriodicChartDerivative.normalization a c hc x inside).toContinuousLinearMap‖ ≤ Cf * Bf ∧
    ‖(PeriodicChartDerivative.normalization a c hc x inside).symm.toContinuousLinearMap‖ ≤ Bf * Ci := by
  have hBf : 0 ≤ Bf := (ContinuousLinearMap.opNorm_nonneg _).trans frame.1
  have hCf : 0 ≤ Cf := (ContinuousLinearMap.opNorm_nonneg _).trans forward
  constructor
  · have eq : (PeriodicChartDerivative.normalization a c hc x inside).toContinuousLinearMap =
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x.val)).toContinuousLinearMap.comp
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) c x.val)).comp (a.whole x).toContinuousLinearMap := rfl
    rw [eq]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul forward frame.1 (ContinuousLinearMap.opNorm_nonneg _) hCf)
  · have eq : (PeriodicChartDerivative.normalization a c hc x inside).symm.toContinuousLinearMap =
        (a.whole x).symm.toContinuousLinearMap.comp
          (((CompactRiemannianChartBounds.chart_differentiable c hc).mfderiv inside).symm.toContinuousLinearMap.comp
            (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x.val)).symm.toContinuousLinearMap) := rfl
    rw [eq]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul frame.2 inverse (ContinuousLinearMap.opNorm_nonneg _) hBf)

end LeanShared.PeriodicChartChains
