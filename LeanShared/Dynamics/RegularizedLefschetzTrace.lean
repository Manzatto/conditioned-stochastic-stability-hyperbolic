module
public import LeanShared.Dynamics.RegularizedLefschetzLocalize

/-! The regularized Lefschetz trace of a weighted hyperbolic dynamics. For every
relative accuracy `η` there is a scale `ε₀` such that for all kernels at scales `ε ≤ ε₀`
(nonnegative, continuous, compactly supported in the `ε`-ball, of unit mass) and all
times `n = N m`, the regularized chart trace `Σ_i ∫ c_i(φ_i⁻¹z) g_n(φ_i⁻¹z) κ(φ_i(T^n φ_i⁻¹z) - z) dz`
is within `η Lef_n` of the Lefschetz sum `Lef_n = Σ_{T^n p = p} g_n(p)/|det(1 - DT^n_p)|`,
uniformly in `n`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Bundle Metric MeasureTheory Filter
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

theorem cutoff_le_one (i : s.charts.ι) (x : M) (hx : x ∈ Λ) : s.cutoff i x ≤ 1 := by
  let := s.charts.fintype
  have sum := s.cutoff_sum x hx
  rw [← sum]
  exact Finset.single_le_sum (f := fun j => s.cutoff j x) (fun j _ => s.cutoff_nonneg j x)
    (Finset.mem_univ i)

/-- The base Lefschetz determinant of a chain is the literal periodic denominator. -/
theorem chain_denominator (N m : ℕ) (i : s.charts.ι) (lam : ℝ) {p : Λ}
    (pc : PeriodicChain s.frame s.charts ((T ^ N : M ≃ₜ M) : M → M) lam p m i)
    (δD : ℝ≥0) (hδD : 0 < δD) (small' : pc.chain.k + δD * 2 < 1)
    (fixed : (T : M → M)^[N * m] p.val = p.val) :
    |LinearMap.det ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin s.frame.unstableDimension) ×
        EuclideanSpace ℝ (Fin s.frame.stableDimension)) - CyclicHyperbolicDeterminant.prodFrom
      (pc.chain.toData δD hδD small').D 0 (pc.chain.toData δD hδD small').period) :
        (EuclideanSpace ℝ (Fin s.frame.unstableDimension) ×
          EuclideanSpace ℝ (Fin s.frame.stableDimension)) →ₗ[ℝ] _)| =
      DiffeomorphismDifferential.periodicDenominator T (s.forward.mdifferentiable one_ne_zero)
        (s.inverse.mdifferentiable one_ne_zero) (N * m) p.val fixed := by
  have Hsmooth : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T ^ N : M ≃ₜ M) : M → M) :=
    DiffeomorphismIterates.mdifferentiable_pow T (s.forward.mdifferentiable one_ne_zero) N
  have hX : ∀ v, (DiffeomorphismDifferential.periodicReturn T (s.forward.mdifferentiable one_ne_zero)
      (s.inverse.mdifferentiable one_ne_zero) (N * m) p.val fixed).toContinuousLinearMap v =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (((T ^ N : M ≃ₜ M) : M → M)^[m]) p.val v := by
    intro v
    rw [ContinuousLinearEquiv.coe_coe, DiffeomorphismDifferential.periodicReturn_apply]
    have same : ((T ^ N : M ≃ₜ M) : M → M)^[m] = (T : M → M)^[N * m] := by
      funext x
      exact iterate_block N m x
    rw [same]
  have eq := pc.det_eq Hsmooth _ hX
  have hperiod : (pc.chain.toData δD hδD small').period = m := pc.period_eq
  simp only [DiffeomorphismDifferential.periodicDenominator]
  rw [hperiod]
  have hD : (pc.chain.toData δD hδD small').D =
      fun k => (pc.chain.A k : EuclideanSpace ℝ (Fin s.frame.unstableDimension) →L[ℝ] _).prodMap
        (pc.chain.B k) := rfl
  rw [hD, eq]
  rfl

/-- The estimate on one chain region. -/
theorem piece_estimate [MeasurableSpace E] [BorelSpace E] (μE : Measure E) (κ : E → ℝ)
    (N m : ℕ) (i : s.charts.ι) (lam : ℝ) {p : Λ}
    (pc : PeriodicChain s.frame s.charts ((T ^ N : M ≃ₜ M) : M → M) lam p m i)
    (δD : ℝ≥0) (hδD : 0 < δD) (small' : pc.chain.k + δD * 2 < 1)
    (fixed : (T : M → M)^[N * m] p.val = p.val) (ρ cl α τ : ℝ) (hτ : 0 ≤ τ) (hclτ : cl * ρ ^ α ≤ τ)
    (est : ∀ G : M → ℝ, Continuous G → ∀ ηG : ℝ,
      (∀ w ∈ (pc.chain.toData δD hδD small').region,
        ‖(pc.chain.toData δD hδD small').closing w‖ ≤ ρ → |G (pc.decode w) - G p.val| ≤ ηG) →
      abs (∫ z in pc.affine ⁻¹' (pc.chain.toData δD hδD small').region,
          G ((s.charts.chart i).symm z) *
            κ (s.charts.chart i (((T ^ N : M ≃ₜ M) : M → M)^[m] ((s.charts.chart i).symm z)) - z)
            ∂μE -
        G p.val / abs (LinearMap.det ((ContinuousLinearMap.id ℝ
          (EuclideanSpace ℝ (Fin s.frame.unstableDimension) ×
            EuclideanSpace ℝ (Fin s.frame.stableDimension)) - CyclicHyperbolicDeterminant.prodFrom
          (pc.chain.toData δD hδD small').D 0 (pc.chain.toData δD hδD small').period) :
            (EuclideanSpace ℝ (Fin s.frame.unstableDimension) ×
              EuclideanSpace ℝ (Fin s.frame.stableDimension)) →ₗ[ℝ] _))) ≤
        2 * (ηG + cl * ρ ^ α * abs (G p.val)) /
          abs (LinearMap.det ((ContinuousLinearMap.id ℝ
          (EuclideanSpace ℝ (Fin s.frame.unstableDimension) ×
            EuclideanSpace ℝ (Fin s.frame.stableDimension)) - CyclicHyperbolicDeterminant.prodFrom
          (pc.chain.toData δD hδD small').D 0 (pc.chain.toData δD hδD small').period) :
            (EuclideanSpace ℝ (Fin s.frame.unstableDimension) ×
              EuclideanSpace ℝ (Fin s.frame.stableDimension)) →ₗ[ℝ] _)))
    (weightClose : ∀ w ∈ (pc.chain.toData δD hδD small').region,
      ‖(pc.chain.toData δD hδD small').closing w‖ ≤ ρ →
      |weightProduct T s.weight (N * m) (pc.decode w) - weightProduct T s.weight (N * m) p.val| ≤
        τ * weightProduct T s.weight (N * m) p.val)
    (cutClose : ∀ w ∈ (pc.chain.toData δD hδD small').region,
      ‖(pc.chain.toData δD hδD small').closing w‖ ≤ ρ →
      |s.cutoff i (pc.decode w) - s.cutoff i p.val| ≤ τ) :
    |∫ z in pc.affine ⁻¹' (pc.chain.toData δD hδD small').region, s.integrand κ (N * m) i z ∂μE -
        s.cutoff i p.val * weightProduct T s.weight (N * m) p.val /
          DiffeomorphismDifferential.periodicDenominator T (s.forward.mdifferentiable one_ne_zero)
            (s.inverse.mdifferentiable one_ne_zero) (N * m) p.val fixed| ≤
      2 * (τ * (3 + τ)) * weightProduct T s.weight (N * m) p.val /
        DiffeomorphismDifferential.periodicDenominator T (s.forward.mdifferentiable one_ne_zero)
          (s.inverse.mdifferentiable one_ne_zero) (N * m) p.val fixed := by
  set d := pc.chain.toData δD hδD small'
  set A := pc.affine ⁻¹' d.region
  set gp := weightProduct T s.weight (N * m) p.val
  have gp0 : 0 ≤ gp := Finset.prod_nonneg fun l _ => s.weight_nonneg _
  have cp0 : 0 ≤ s.cutoff i p.val := s.cutoff_nonneg i p.val
  have cp1 : s.cutoff i p.val ≤ 1 := s.cutoff_le_one i p.val p.property
  set G : M → ℝ := fun x => s.cutoff i x * weightProduct T s.weight (N * m) x
  have Gc : Continuous G := by
    apply (s.cutoff_continuous i).mul
    unfold weightProduct
    exact continuous_finsetProd _ fun l _ => s.weight_continuous.comp (T.continuous.iterate l)
  have closeG : ∀ w ∈ d.region, ‖d.closing w‖ ≤ ρ →
      |G (pc.decode w) - G p.val| ≤ τ * (2 + τ) * gp := by
    intro w hw hρ
    have wc := weightClose w hw hρ
    have cc := cutClose w hw hρ
    set gx := weightProduct T s.weight (N * m) (pc.decode w)
    have gx0 : 0 ≤ gx := Finset.prod_nonneg fun l _ => s.weight_nonneg _
    have gxle : gx ≤ (1 + τ) * gp := by
      have := (abs_le.mp wc).2
      linarith
    have split : G (pc.decode w) - G p.val =
        (s.cutoff i (pc.decode w) - s.cutoff i p.val) * gx + s.cutoff i p.val * (gx - gp) := by
      simp only [G, gx, gp]
      ring
    rw [split]
    calc |(s.cutoff i (pc.decode w) - s.cutoff i p.val) * gx + s.cutoff i p.val * (gx - gp)|
        ≤ |s.cutoff i (pc.decode w) - s.cutoff i p.val| * gx + s.cutoff i p.val * |gx - gp| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg gx0, abs_of_nonneg cp0]
      _ ≤ τ * ((1 + τ) * gp) + 1 * (τ * gp) := by
          apply add_le_add
          · exact mul_le_mul cc gxle gx0 hτ
          · exact mul_le_mul cp1 wc (abs_nonneg _) zero_le_one
      _ = τ * (2 + τ) * gp := by ring
  have main := est G Gc (τ * (2 + τ) * gp) closeG
  rw [s.chain_denominator N m i lam pc δD hδD small' fixed] at main
  have formula : ∫ z in A, s.integrand κ (N * m) i z ∂μE =
      ∫ z in A, G ((s.charts.chart i).symm z) *
        κ (s.charts.chart i (((T ^ N : M ≃ₜ M) : M → M)^[m] ((s.charts.chart i).symm z)) - z) ∂μE :=
    setIntegral_congr_fun ((d.isClosed_region.preimage pc.affine.continuous).measurableSet)
      fun z hz => s.integrand_on_region κ N m i lam pc δD hδD small' z hz
  rw [formula]
  set den := DiffeomorphismDifferential.periodicDenominator T (s.forward.mdifferentiable one_ne_zero)
    (s.inverse.mdifferentiable one_ne_zero) (N * m) p.val fixed
  have den0 : 0 ≤ den := abs_nonneg _
  have Gp : G p.val = s.cutoff i p.val * gp := rfl
  have absGp : |G p.val| ≤ gp := by
    rw [Gp, abs_mul, abs_of_nonneg cp0, abs_of_nonneg gp0]
    exact mul_le_of_le_one_left gp0 cp1
  refine main.trans ?_
  rw [Gp] at main ⊢
  apply div_le_div_of_nonneg_right _ den0
  have : cl * ρ ^ α * |s.cutoff i p.val * gp| ≤ τ * gp := by
    rw [← Gp]
    by_cases hcl : 0 ≤ cl * ρ ^ α
    · exact mul_le_mul hclτ absGp (abs_nonneg _) hτ
    · push Not at hcl
      calc cl * ρ ^ α * |G p.val| ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcl.le (abs_nonneg _)
        _ ≤ τ * gp := mul_nonneg hτ gp0
  nlinarith

/-- A function continuous at zero and vanishing there is small near zero. -/
theorem exists_small_scale (f : ℝ → ℝ) (continuous : ContinuousAt f 0) (zero : f 0 = 0)
    (c : ℝ) (hc : 0 < c) : ∃ ρs : ℝ, 0 < ρs ∧ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ ρs → f ρ < c := by
  have ev : ∀ᶠ ρ in 𝓝 (0 : ℝ), f ρ < c := continuous.eventually (gt_mem_nhds (by rw [zero]; exact hc))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp ev
  refine ⟨δ / 2, by positivity, fun ρ h0 h1 => hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

/-- The integrand is integrable on chain regions. -/
theorem integrableOn_region [MeasurableSpace E] [BorelSpace E] (μE : Measure E)
    [μE.IsAddHaarMeasure] (κ : E → ℝ) (hκ : Continuous κ)
    (N m : ℕ) (i : s.charts.ι) (lam : ℝ) {p : Λ}
    (pc : PeriodicChain s.frame s.charts ((T ^ N : M ≃ₜ M) : M → M) lam p m i)
    (δD : ℝ≥0) (hδD : 0 < δD) (small' : pc.chain.k + δD * 2 < 1) :
    IntegrableOn (s.integrand κ (N * m) i) (pc.affine ⁻¹' (pc.chain.toData δD hδD small').region) μE := by
  set d := pc.chain.toData δD hδD small'
  set A := pc.affine ⁻¹' d.region
  have bounded : Bornology.IsBounded d.region := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    exact ⟨d.r, fun w hw => by
      simpa only [Metric.mem_closedBall, dist_zero_right, LocalPeriodicClosing.Data.orbit_zero]
        using hw 0 (Nat.zero_le _)⟩
  have compactRegion : IsCompact d.region :=
    Metric.isCompact_of_isClosed_isBounded d.isClosed_region bounded
  have compactA : IsCompact A := by
    have : A = pc.affine.symm '' d.region := by
      ext z
      simp only [A, Set.mem_preimage, Set.mem_image]
      exact ⟨fun h => ⟨pc.affine z, h, pc.affine.symm_apply_apply z⟩,
        fun ⟨w, hw, hz⟩ => by rw [← hz, pc.affine.apply_symm_apply]; exact hw⟩
    rw [this]
    exact compactRegion.image pc.affine.symm.continuous
  -- the integrand agrees with a continuous formula on the region
  have hr := pc.chain.radius_pos δD hδD
  have targetA (z : E) (hz : z ∈ A) : z ∈ (s.charts.chart i).target := by
    have hw : pc.affine z ∈ d.region := hz
    have hw0 : ‖pc.affine z‖ ≤ 2 * pc.chain.radius δD := by
      have := hw 0 (Nat.zero_le _)
      change ‖pc.affine z‖ ≤ pc.chain.radius δD at this
      linarith
    have mem := pc.chart_symm_mem 0 _ (pc.ball_of_radius δD 0 _ hw0)
    rw [pc.σ_zero] at mem
    have eq : pc.chain.a 0 + pc.chain.L 0 (pc.affine z) = z := by
      simp only [PeriodicChain.affine_apply, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
    rw [eq] at mem
    rw [← mem.2]
    exact (s.charts.chart i).map_source mem.1
  have sourceA (z : E) (hz : z ∈ A) : ((T ^ N : M ≃ₜ M) : M → M)^[m] ((s.charts.chart i).symm z) ∈
      (s.charts.chart i).source := by
    have hw : pc.affine z ∈ d.region := hz
    have last := (pc.orbit_eq δD hδD small' _ hw m le_rfl).1
    have σm : pc.σ (m : ℤ) = i := by
      have := pc.periodic_σ 0
      rwa [zero_add, pc.σ_zero] at this
    have decodeEq : pc.decode (pc.affine z) = (s.charts.chart i).symm z := by
      simp only [PeriodicChain.decode, PeriodicChain.affine_apply,
        ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
    rwa [σm, decodeEq] at last
  have formulaC : ContinuousOn (fun z => (s.cutoff i ((s.charts.chart i).symm z) *
      weightProduct T s.weight (N * m) ((s.charts.chart i).symm z)) *
      κ (s.charts.chart i (((T ^ N : M ≃ₜ M) : M → M)^[m] ((s.charts.chart i).symm z)) - z)) A := by
    have symmC : ContinuousOn (s.charts.chart i).symm A :=
      (s.charts.chart i).continuousOn_symm.mono targetA
    have gC : Continuous (fun x => s.cutoff i x * weightProduct T s.weight (N * m) x) := by
      apply (s.cutoff_continuous i).mul
      unfold weightProduct
      exact continuous_finsetProd _ fun l _ => s.weight_continuous.comp (T.continuous.iterate l)
    have iterC : ContinuousOn (fun z => ((T ^ N : M ≃ₜ M) : M → M)^[m] ((s.charts.chart i).symm z)) A :=
      ((T ^ N).continuous.iterate m).comp_continuousOn symmC
    have chartC : ContinuousOn (fun z => s.charts.chart i
        (((T ^ N : M ≃ₜ M) : M → M)^[m] ((s.charts.chart i).symm z))) A :=
      (s.charts.chart i).continuousOn.comp iterC sourceA
    exact (gC.comp_continuousOn symmC).mul (hκ.comp_continuousOn (chartC.sub continuousOn_id))
  have integrableFormula := formulaC.integrableOn_compact (μ := μE) compactA
  refine integrableFormula.congr_fun (fun z hz => ?_) ((d.isClosed_region.preimage
    pc.affine.continuous).measurableSet)
  exact (s.integrand_on_region κ N m i lam pc δD hδD small' z hz).symm

end TraceSetup
end LeanShared.HyperbolicBasicSet
