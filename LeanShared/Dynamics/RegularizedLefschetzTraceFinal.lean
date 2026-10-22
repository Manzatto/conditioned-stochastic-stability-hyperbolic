module
public import LeanShared.Dynamics.RegularizedLefschetzTrace
public import LeanShared.Dynamics.PeriodicChartChainExistence

/-! The regularized Lefschetz trace comparison (final assembly). -/
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

/-- The constants of the chains are those of the uniform construction. -/
theorem chain_radius {N : ℕ} {lam : ℝ} {p : Λ} {m : ℕ} {i : s.charts.ι}
    (pc : PeriodicChain s.frame s.charts ((T ^ N : M ≃ₜ M) : M → M) lam p m i)
    (ρ0 bound holderC α : ℝ) (hρ : pc.chain.ρ = ρ0) (hb : pc.chain.bound = bound)
    (hC : pc.chain.holderC = holderC) (hα : pc.chain.α = α) (δ : ℝ) :
    pc.chain.radius δ = min (ρ0 / (2 * bound))
      ((δ / (bound ^ 2 * holderC * bound ^ α + 1)) ^ α⁻¹) ∧
    pc.chain.holderK = bound ^ 2 * holderC * bound ^ α := by
  simp only [ChartChainClosing.Chain.radius, ChartChainClosing.Chain.holderK, hρ, hb, hC, hα,
    and_self]

set_option maxHeartbeats 8000000 in
/-- The regularized Lefschetz trace comparison. -/
theorem trace_close [MeasurableSpace E] [BorelSpace E] (μE : Measure E) [μE.IsAddHaarMeasure] :
    ∃ N : ℕ, 0 < N ∧ ∀ η : ℝ, 0 < η → ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε0 →
      ∀ κ : E → ℝ, Continuous κ → (∀ z, 0 ≤ κ z) → HasCompactSupport κ →
      (∀ z, ε < ‖z‖ → κ z = 0) → ∫ z, κ z ∂μE = 1 →
      ∀ m : ℕ, 0 < m →
        |s.trace μE κ (N * m) - b.periodicLefschetzSum s.forward s.inverse s.weight (N * m)| ≤
          η * b.periodicLefschetzSum s.forward s.inverse s.weight (N * m) := by
  classical
  let := s.charts.fintype
  obtain ⟨N, hN, lam, ρ0, bound, holderC, α, hlam, hρ0, hbound, hC0, hα, hα1, chains⟩ :=
    PeriodicChartChains.exists_periodic_chains s.frame s.charts s.cover
      (s.forward.mdifferentiable one_ne_zero) (s.inverse.mdifferentiable one_ne_zero)
      s.one_lt_r s.regular
  refine ⟨N, hN, fun η hη => ?_⟩
  set K := bound ^ 2 * holderC * bound ^ α with hKdef
  have hK : 0 ≤ K := by positivity
  -- expansivity and moduli
  obtain ⟨δdis, hδdis, unique⟩ := b.periodic_unique s.forward s.inverse
  obtain ⟨sb, hsb, iterClose⟩ := uniform_iterates T N (δdis / 2) (by positivity)
  obtain ⟨sc, hsc, chartSymm⟩ := uniform_chart_symm s.charts sb hsb
  -- the data closeness
  set δval : ℝ := min (1 / 4) ((sc / bound) ^ α * (K + 1))
  have hδval : 0 < δval := lt_min (by norm_num) (by positivity)
  set δD : ℝ≥0 := ⟨δval, hδval.le⟩
  have hδD : 0 < δD := hδval
  have small : (1 / 8 : ℝ≥0) + δD * 2 < 1 := by
    have h1 : (δD : ℝ) ≤ 1 / 4 := min_le_left _ _
    have h : ((1 / 8 : ℝ≥0) : ℝ) + (δD : ℝ) * 2 < 1 := by
      push_cast
      linarith
    exact_mod_cast h
  set rD : ℝ := min (ρ0 / (2 * bound)) ((δval / (K + 1)) ^ α⁻¹)
  have hrD : 0 < rD := lt_min (by positivity) (Real.rpow_pos_of_pos (by positivity) _)
  have boundRD : bound * rD ≤ sc := by
    have h1 : rD ≤ (δval / (K + 1)) ^ α⁻¹ := min_le_right _ _
    have h2 : δval / (K + 1) ≤ (sc / bound) ^ α := by
      rw [div_le_iff₀ (by positivity)]
      exact min_le_right _ _
    have h3 : (δval / (K + 1)) ^ α⁻¹ ≤ ((sc / bound) ^ α) ^ α⁻¹ :=
      Real.rpow_le_rpow (by positivity) h2 (by positivity)
    rw [Real.rpow_rpow_inv (by positivity) hα.ne'] at h3
    calc bound * rD ≤ bound * (sc / bound) := mul_le_mul_of_nonneg_left (h1.trans h3) hbound.le
      _ = sc := by field_simp
  -- local estimate constants
  obtain ⟨cl, ρ1, hcl, hρ1, localEst⟩ := PeriodicChartChains.exists_local_estimate
    (a := s.frame) (F := s.charts) (H := ((T ^ N : M ≃ₜ M) : M → M)) (lam := lam)
    (1 / 8) δD hδD small K α hK hα hα1.le
  set CD : ℝ := (((1 / 8 : ℝ≥0) : ℝ) + 1) / (1 - ((1 / 8 : ℝ≥0) + δD * 2 : ℝ≥0))
  have hCD : 0 ≤ CD := by
    have : (((1 / 8 : ℝ≥0) + δD * 2 : ℝ≥0) : ℝ) < 1 := by exact_mod_cast small
    exact div_nonneg (by positivity) (by linarith)
  set θ := HyperbolicConeCloseness.rate ((1 / 8 : ℝ≥0) : ℝ) (δD : ℝ)
  -- weight ratio
  have invariant : ∀ x ∈ Λ, T x ∈ Λ := fun x hx => by
    rw [← b.hyperbolic.invariant]
    exact mem_image_of_mem T hx
  obtain ⟨Rw, Cw, hRw, hCw, ratio⟩ := PeriodicChartChains.exists_weight_ratio s.charts T Λ
    b.hyperbolic.compact invariant N s.weight s.weight_continuous s.weight_pos s.q_pos s.q_lt_one
    s.weight_regular lam hlam
  -- localization constants
  obtain ⟨sf, hsf, chartFwd⟩ := uniform_chart s.charts (rD / bound) (by positivity)
  set δloc := min (min lam sf) s.margin
  have hδloc : 0 < δloc := lt_min (lt_min hlam hsf) s.margin_pos
  obtain ⟨ε1, hε1, shadow⟩ := b.periodic_closing_shadow s.forward s.inverse δloc hδloc
  obtain ⟨εm, hεm, markedMargin⟩ := marked_margin s.charts
  obtain ⟨sε, hsε, chartClose⟩ := uniform_chart_symm s.charts ε1 hε1
  -- accuracy
  set card : ℝ := (Fintype.card s.charts.ι : ℝ)
  have hcard : 0 ≤ card := Nat.cast_nonneg _
  set τ : ℝ := min 1 (η / (8 * (card + 1)))
  have hτ : 0 < τ := lt_min one_pos (by positivity)
  have cutEach (i : s.charts.ι) := uniform_function (s.cutoff i) (s.cutoff_continuous i) τ hτ
  choose scut hscut cutMod using cutEach
  obtain ⟨scut0, hscut0, hscutle⟩ := exists_uniform_lower scut hscut
  obtain ⟨sc2, hsc2, chartSymm2⟩ := uniform_chart_symm s.charts scut0 hscut0
  -- small scales
  set Xf : ℝ → ℝ := fun ρ => N * (Cw * (bound * ((CD + 1) * ρ)) ^ s.q) * (2 / (1 - θ ^ s.q))
  have rpowCont (c0 : ℝ) : ContinuousAt (fun ρ : ℝ => (c0 * ρ) ^ s.q) 0 :=
    (continuousAt_const.mul continuousAt_id).rpow_const (Or.inr s.q_pos.le)
  have rpowZero (c0 : ℝ) : (c0 * (0 : ℝ)) ^ s.q = 0 := by
    rw [mul_zero, Real.zero_rpow s.q_pos.ne']
  obtain ⟨r1, hr1, c1⟩ := exists_small_scale (fun ρ => ρ) continuousAt_id rfl ρ1 hρ1
  obtain ⟨r2, hr2, c2⟩ := exists_small_scale (fun ρ => (CD + 1) * ρ)
    (continuousAt_const.mul continuousAt_id) (by simp) rD hrD
  obtain ⟨r3, hr3, c3⟩ := exists_small_scale (fun ρ => 2 * (bound * ((CD + 1) * ρ)))
    (by fun_prop) (by simp) Rw hRw
  obtain ⟨r4, hr4, c4⟩ := exists_small_scale
    (fun ρ => Cw * (2 * (bound * ((CD + 1) * ρ))) ^ s.q)
    (by
      have := (rpowCont (2 * (bound * (CD + 1)))).const_mul Cw
      refine this.congr (Eventually.of_forall fun ρ => ?_)
      simp only
      ring_nf)
    (by simp only [mul_zero]; rw [Real.zero_rpow s.q_pos.ne', mul_zero]) (1 / 2) (by norm_num)
  obtain ⟨r5, hr5, c5⟩ := exists_small_scale (fun ρ => Real.exp 2 * (2 * Xf ρ))
    (by
      have := (((rpowCont (bound * (CD + 1))).const_mul Cw).const_mul (N : ℝ)).mul_const
        (2 / (1 - θ ^ s.q))
      have := (this.const_mul 2).const_mul (Real.exp 2)
      refine this.congr (Eventually.of_forall fun ρ => ?_)
      simp only [Xf]
      ring_nf)
    (by simp only [Xf, mul_zero]; rw [Real.zero_rpow s.q_pos.ne']; ring)
    (min τ 2) (lt_min hτ (by norm_num))
  obtain ⟨r6, hr6, c6⟩ := exists_small_scale (fun ρ => bound * (2 * ((CD + 1) * ρ)))
    (by fun_prop) (by simp) sc2 hsc2
  obtain ⟨r7, hr7, c7⟩ := exists_small_scale (fun ρ => cl * ρ ^ α)
    (continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr hα.le)))
    (by rw [Real.zero_rpow hα.ne', mul_zero]) τ hτ
  set ρs := min r1 (min r2 (min r3 (min r4 (min r5 (min r6 r7)))))
  have hρs : 0 < ρs := lt_min hr1 (lt_min hr2 (lt_min hr3 (lt_min hr4 (lt_min hr5 (lt_min hr6 hr7)))))
  set ε0 := min (min εm sε) (ρs / bound)
  have hε0pos : 0 < ε0 := lt_min (lt_min hεm hsε) (by positivity)
  refine ⟨ε0, hε0pos, fun ε hε hε0 κ hκ hκ0 hκc support mass m hm => ?_⟩
  set ρ := bound * ε
  have hρ0 : 0 ≤ ρ := by positivity
  have hρs' : ρ ≤ ρs := by
    have : ε ≤ ρs / bound := hε0.trans (min_le_right _ _)
    calc ρ = bound * ε := rfl
      _ ≤ bound * (ρs / bound) := mul_le_mul_of_nonneg_left this hbound.le
      _ = ρs := by field_simp
  have C1 := c1 ρ hρ0 (hρs'.trans (min_le_left _ _))
  have C2 := c2 ρ hρ0 (hρs'.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have C3 := c3 ρ hρ0 (hρs'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _))))
  have C4 := c4 ρ hρ0 (hρs'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))))
  have C5 := c5 ρ hρ0 (hρs'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
  have C6 := c6 ρ hρ0 (hρs'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _)))))))
  have C7 := c7 ρ hρ0 (hρs'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _)))))))
  have hεm' : ε ≤ εm := hε0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεs' : ε ≤ sε := hε0.trans ((min_le_left _ _).trans (min_le_right _ _))
  -- chains at all marked periodic points
  have pickChain : ∀ (i : s.charts.ι) (p : Λ),
      ((T ^ N : M ≃ₜ M) : M → M)^[m] p.val = p.val → p.val ∈ s.charts.marked i →
      ∃ c : PeriodicChain s.frame s.charts ((T ^ N : M ≃ₜ M) : M → M) lam p m i,
        c.chain.ρ = ρ0 ∧ c.chain.bound = bound ∧ c.chain.holderC = holderC ∧ c.chain.α = α ∧
          c.chain.k = 1 / 8 :=
    fun i p hfix hmk => chains p m hm hfix i hmk
  choose chainOf hcρ hcb hcC hcα hck using pickChain
  have smallOf (i : s.charts.ι) (p : Λ) (hfix) (hmk) :
      (chainOf i p hfix hmk).chain.k + δD * 2 < 1 := by
    rw [hck]
    exact small
  have radiusOf (i : s.charts.ι) (p : Λ) (hfix) (hmk) :
      (chainOf i p hfix hmk).chain.radius δD = rD ∧ (chainOf i p hfix hmk).chain.holderK = K :=
    s.chain_radius (chainOf i p hfix hmk) ρ0 bound holderC α (hcρ i p hfix hmk) (hcb i p hfix hmk)
      (hcC i p hfix hmk) (hcα i p hfix hmk) δD
  have constantOf (i : s.charts.ι) (p : Λ) (hfix) (hmk) :
      ((chainOf i p hfix hmk).chain.toData δD hδD (smallOf i p hfix hmk)).constant = CD := by
    simp only [LocalPeriodicClosing.Data.constant, ChartChainClosing.Chain.toData, hck, CD]
  have rateOf (i : s.charts.ι) (p : Λ) (hfix) (hmk) :
      HyperbolicConeCloseness.rate ((chainOf i p hfix hmk).chain.toData δD hδD (smallOf i p hfix hmk)).k
        ((chainOf i p hfix hmk).chain.toData δD hδD (smallOf i p hfix hmk)).δ = θ := by
    simp only [ChartChainClosing.Chain.toData, hck, θ]
  have hθ1 : θ < 1 := HyperbolicConeCloseness.rate_lt_one _ _ (by positivity) (by positivity) (by
    have : (((1 / 8 : ℝ≥0) + δD * 2 : ℝ≥0) : ℝ) < 1 := by exact_mod_cast small
    push_cast at this ⊢
    linarith [δD.coe_nonneg])
  have hθ0 : 0 ≤ θ := HyperbolicConeCloseness.rate_nonneg _ _ (by positivity) (by positivity)
  -- the per-piece bound
  have pieceBound : ∀ (i : s.charts.ι) (p : Λ) (hfix) (hmk)
      (fixed : (T : M → M)^[N * m] p.val = p.val),
      |∫ z in (chainOf i p hfix hmk).affine ⁻¹'
          ((chainOf i p hfix hmk).chain.toData δD hδD (smallOf i p hfix hmk)).region,
          s.integrand κ (N * m) i z ∂μE -
        s.cutoff i p.val * weightProduct T s.weight (N * m) p.val /
          DiffeomorphismDifferential.periodicDenominator T (s.forward.mdifferentiable one_ne_zero)
            (s.inverse.mdifferentiable one_ne_zero) (N * m) p.val fixed| ≤
        2 * (τ * (3 + τ)) * weightProduct T s.weight (N * m) p.val /
          DiffeomorphismDifferential.periodicDenominator T (s.forward.mdifferentiable one_ne_zero)
            (s.inverse.mdifferentiable one_ne_zero) (N * m) p.val fixed := by
    intro i p hfix hmk fixed
    set pc := chainOf i p hfix hmk
    set d := pc.chain.toData δD hδD (smallOf i p hfix hmk)
    have hb := hcb i p hfix hmk
    have hconst := constantOf i p hfix hmk
    have hrate := rateOf i p hfix hmk
    have hrad := (radiusOf i p hfix hmk).1
    have est := localEst pc (smallOf i p hfix hmk) (hck i p hfix hmk) (radiusOf i p hfix hmk).2
      (hcα i p hfix hmk) μE κ hκ hκ0 hκc ε hε support mass (by rw [hb]; exact C1.le)
      (by
        change (d.constant + 1) * (pc.chain.bound * ε) ≤ pc.chain.radius δD
        rw [hconst, hb, hrad]
        exact C2.le)
    rw [hb] at est
    -- weight closeness
    have weightClose : ∀ w ∈ d.region, ‖d.closing w‖ ≤ ρ →
        |weightProduct T s.weight (N * m) (pc.decode w) - weightProduct T s.weight (N * m) p.val| ≤
          τ * weightProduct T s.weight (N * m) p.val := by
      intro w hw hclose
      obtain ⟨R, hRe, lower, upper⟩ := weight_product_close pc δD hδD (smallOf i p hfix hmk)
        s.weight s.weight_pos invariant Rw Cw hCw s.q_pos s.q_lt_one.le ratio w hw ρ hρ0 hclose
        (by rw [hb, hconst]; exact C3.le) (by rw [hb, hconst]; exact C4.le)
      rw [hb, hconst, hrate] at lower upper
      set X := Xf ρ
      have hX0 : 0 ≤ X := by
        have := Real.rpow_nonneg (show 0 ≤ bound * ((CD + 1) * ρ) by positivity) s.q
        have : 0 ≤ 2 / (1 - θ ^ s.q) := by
          have : θ ^ s.q < 1 := Real.rpow_lt_one hθ0 hθ1 s.q_pos
          exact div_nonneg (by norm_num) (by linarith)
        simp only [X, Xf]
        positivity
      have e2 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
      have hC5 : Real.exp 2 * (2 * X) < min τ 2 := C5
      have h2X : 2 * X ≤ 2 := by
        have := hC5.trans_le (min_le_right _ _)
        nlinarith
      have hτX : Real.exp 2 * (2 * X) ≤ τ := (hC5.trans_le (min_le_left _ _)).le
      have upperR : R - 1 ≤ τ := by
        have h1 : Real.exp X ≤ Real.exp (2 * X) := Real.exp_le_exp.mpr (by linarith)
        have h2 := LocalPeriodicClosing.Data.exp_sub_one_le (2 * X) (by linarith) h2X
        linarith
      have lowerR : 1 - R ≤ τ := by
        have h1 := Real.add_one_le_exp (-(2 * X))
        nlinarith
      have gp0 : 0 ≤ weightProduct T s.weight (N * m) p.val :=
        Finset.prod_nonneg fun l _ => s.weight_nonneg _
      rw [hRe, show weightProduct T s.weight (N * m) p.val * R - weightProduct T s.weight (N * m) p.val =
        weightProduct T s.weight (N * m) p.val * (R - 1) by ring, abs_mul, abs_of_nonneg gp0,
        mul_comm]
      exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, upperR⟩) gp0
    -- cutoff closeness
    have cutClose : ∀ w ∈ d.region, ‖d.closing w‖ ≤ ρ →
        |s.cutoff i (pc.decode w) - s.cutoff i p.val| ≤ τ := by
      intro w hw hclose
      have hr := pc.chain.radius_pos δD hδD
      have hw0 : ‖w‖ ≤ 2 * ((CD + 1) * ρ) := by
        have close := d.closeness w hw 0 (Nat.zero_le _)
        rw [hconst, hrate, LocalPeriodicClosing.Data.orbit_zero, pow_zero, Nat.sub_zero] at close
        have tm : θ ^ d.period ≤ 1 := pow_le_one₀ hθ0 hθ1.le
        calc ‖w‖ ≤ (CD + 1) * ‖d.closing w‖ * (1 + θ ^ d.period) := close
          _ ≤ (CD + 1) * ρ * 2 := by
              apply mul_le_mul _ (by linarith) (by positivity) (by positivity)
              exact mul_le_mul_of_nonneg_left hclose (by linarith)
          _ = 2 * ((CD + 1) * ρ) := by ring
      have hwr : ‖w‖ ≤ 2 * pc.chain.radius δD := by
        have := hw 0 (Nat.zero_le _)
        change ‖w‖ ≤ pc.chain.radius δD at this
        linarith
      have ball := pc.ball_of_radius δD 0 w hwr
      have mem1 := image_mono subset_closure (pc.inChart 0 _ ball)
      have mem2 := image_mono subset_closure (pc.inChart 0 _ (mem_closedBall_self pc.chain.ρ_pos.le))
      rw [pc.σ_zero] at mem1 mem2
      have near : ‖(pc.chain.a 0 + pc.chain.L 0 w) - pc.chain.a 0‖ ≤ sc2 := by
        rw [add_sub_cancel_left]
        calc ‖pc.chain.L 0 w‖ ≤ pc.chain.bound * ‖w‖ :=
              ((pc.chain.L 0).toContinuousLinearMap.le_opNorm _).trans
                (mul_le_mul_of_nonneg_right (pc.chain.L_bound 0) (norm_nonneg _))
          _ ≤ bound * (2 * ((CD + 1) * ρ)) := by
              rw [hb]
              exact mul_le_mul_of_nonneg_left hw0 hbound.le
          _ ≤ sc2 := C6.le
      have distance := chartSymm2 i _ mem1 _ mem2 near
      have pEq : (s.charts.chart i).symm (pc.chain.a 0) = p.val := by
        have source := pc.source_point 0
        rw [pc.σ_zero, pc.point_zero] at source
        rw [pc.a_eq 0, pc.σ_zero, pc.point_zero]
        exact (s.charts.chart i).left_inv source
      rw [pEq] at distance
      exact (cutMod i _ _ (distance.trans_le (hscutle i))).le
    exact s.piece_estimate μE κ N m i lam pc δD hδD (smallOf i p hfix hmk) fixed ρ cl α τ hτ.le
      C7.le est weightClose cutClose
  -- periodic points and denominators
  have hn : 0 < N * m := Nat.mul_pos hN hm
  set Per := b.periodicPoints s.forward s.inverse (N * m) hn
  have memPer (x : M) : x ∈ Per ↔ x ∈ Λ ∧ (T : M → M)^[N * m] x = x :=
    b.mem_periodicPoints s.forward s.inverse (N * m) hn x
  set den : M → ℝ := fun x => if h : x ∈ Per then
    DiffeomorphismDifferential.periodicDenominator T (s.forward.mdifferentiable one_ne_zero)
      (s.inverse.mdifferentiable one_ne_zero) (N * m) x ((memPer x).mp h).2 else 1
  set gn : M → ℝ := fun x => weightProduct T s.weight (N * m) x
  have gn0 (x : M) : 0 ≤ gn x := Finset.prod_nonneg fun l _ => s.weight_nonneg _
  have den0 (x : M) : 0 ≤ den x := by
    simp only [den]
    split_ifs
    · exact abs_nonneg _
    · exact zero_le_one
  have hfixOf (x : M) (h : (T : M → M)^[N * m] x = x) : ((T ^ N : M ≃ₜ M) : M → M)^[m] x = x := by
    rw [iterate_block]
    exact h
  -- the chart estimate
  have chartEstimate (i : s.charts.ι) :
      |∫ z, s.integrand κ (N * m) i z ∂μE - ∑ x ∈ Per, s.cutoff i x * gn x / den x| ≤
        ∑ x ∈ Per, 2 * (τ * (3 + τ)) * gn x / den x := by
    set Pi := Per.filter (fun x => x ∈ s.charts.marked i)
    have factsOf (x : M) (hx : x ∈ Pi) : x ∈ Λ ∧ (T : M → M)^[N * m] x = x ∧ x ∈ s.charts.marked i := by
      have h := Finset.mem_filter.mp hx
      exact ⟨((memPer x).mp h.1).1, ((memPer x).mp h.1).2, h.2⟩
    set A : M → Set E := fun x => if hx : x ∈ Pi then
      (chainOf i ⟨x, (factsOf x hx).1⟩ (hfixOf x (factsOf x hx).2.1) (factsOf x hx).2.2).affine ⁻¹'
        ((chainOf i ⟨x, (factsOf x hx).1⟩ (hfixOf x (factsOf x hx).2.1)
          (factsOf x hx).2.2).chain.toData δD hδD
          (smallOf i _ (hfixOf x (factsOf x hx).2.1) (factsOf x hx).2.2)).region else ∅
    have measurableA : ∀ x ∈ Pi, MeasurableSet (A x) := by
      intro x hx
      simp only [A, hx, ↓reduceDIte]
      exact (LocalPeriodicClosing.Data.isClosed_region _).preimage
        (PeriodicChain.affine _).continuous |>.measurableSet
    have disjointA : Set.PairwiseDisjoint (Pi : Set M) A := by
      intro x hx y hy hxy
      rw [Function.onFun, Set.disjoint_left]
      intro z hzx hzy
      apply hxy
      simp only [A, Finset.mem_coe.mp hx, Finset.mem_coe.mp hy, ↓reduceDIte] at hzx hzy
      have shx := s.region_shadow N m i lam _ δD hδD _ z hzx δdis sb sc iterClose chartSymm (by
        rw [hcb, (radiusOf _ _ _ _).1]
        exact boundRD)
      have shy := s.region_shadow N m i lam _ δD hδD _ z hzy δdis sb sc iterClose chartSymm (by
        rw [hcb, (radiusOf _ _ _ _).1]
        exact boundRD)
      have fx := factsOf x (Finset.mem_coe.mp hx)
      have fy := factsOf y (Finset.mem_coe.mp hy)
      exact unique (N * m) hn x fx.1 y fy.1 fx.2.1 fy.2.1 fun l hl => by
        have h1 := shx l hl
        have h2 := shy l hl
        calc dist ((T : M → M)^[l] x) ((T : M → M)^[l] y) ≤
            dist ((T : M → M)^[l] x) ((T : M → M)^[l] ((s.charts.chart i).symm z)) +
              dist ((T : M → M)^[l] ((s.charts.chart i).symm z)) ((T : M → M)^[l] y) :=
              dist_triangle _ _ _
          _ ≤ δdis := by rw [dist_comm] at h1; linarith
    have integrableA : ∀ x ∈ Pi, IntegrableOn (s.integrand κ (N * m) i) (A x) μE := by
      intro x hx
      simp only [A, hx, ↓reduceDIte]
      exact s.integrableOn_region μE κ hκ N m i lam _ δD hδD _
    have vanish : ∀ z, z ∉ ⋃ x ∈ Pi, A x → s.integrand κ (N * m) i z = 0 := by
      intro z hz
      by_contra hne
      obtain ⟨p, hfix, hmk, mem⟩ := s.localize_in_chain κ N m i z ε support hne lam δloc ε1 εm sε
        ((min_le_left _ _).trans (min_le_left _ _)) (min_le_right _ _) hεm' hεs' (markedMargin i)
        (chartClose i)
        (fun x hx hclose => shadow (N * m) hn x hx hclose) δD hδD (fun p hfix hmk => chainOf i p hfix hmk)
        (fun p hfix hmk => smallOf i p hfix hmk)
        (fun c u hu v hv hdist p hfix hmk => by
          rw [(radiusOf i p hfix hmk).1, hcb]
          exact chartFwd c u hu v hv (hdist.trans_le ((min_le_left _ _).trans (min_le_right _ _))))
      apply hz
      have pPer : p.val ∈ Pi := by
        refine Finset.mem_filter.mpr ⟨(memPer _).mpr ⟨p.property, ?_⟩, hmk⟩
        rw [← iterate_block]
        exact hfix
      refine Set.mem_iUnion₂.mpr ⟨p.val, pPer, ?_⟩
      simp only [A, pPer, ↓reduceDIte]
      exact mem
    have decomposition := IntegralDisjointPieces.integral_eq_sum Pi A measurableA disjointA
      (s.integrand κ (N * m) i) integrableA vanish
    -- outside the marked set the cutoff vanishes
    have zeroOutside : ∀ x ∈ Per.filter (fun x => ¬ x ∈ s.charts.marked i),
        s.cutoff i x * gn x / den x = 0 := by
      intro x hx
      have notMarked := (Finset.mem_filter.mp hx).2
      have c0 : s.cutoff i x = 0 := by
        by_contra hc
        exact notMarked (s.cutoff_margin i (self_subset_cthickening _ (subset_tsupport _ hc)))
      rw [c0, zero_mul, zero_div]
    have splitSum := Finset.sum_filter_add_sum_filter_not Per (fun x => x ∈ s.charts.marked i)
      (fun x => s.cutoff i x * gn x / den x)
    rw [Finset.sum_eq_zero zeroOutside, add_zero] at splitSum
    rw [decomposition, ← splitSum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ x ∈ Pi, |∫ z in A x, s.integrand κ (N * m) i z ∂μE - s.cutoff i x * gn x / den x|
        ≤ ∑ x ∈ Pi, 2 * (τ * (3 + τ)) * gn x / den x := by
          refine Finset.sum_le_sum fun x hx => ?_
          have f := factsOf x hx
          have bound := pieceBound i ⟨x, f.1⟩ (hfixOf x f.2.1) f.2.2 f.2.1
          have hxPer : x ∈ Per := (Finset.mem_filter.mp hx).1
          simp only [A, hx, den, hxPer, gn, ↓reduceDIte]
          exact bound
      _ ≤ ∑ x ∈ Per, 2 * (τ * (3 + τ)) * gn x / den x :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ =>
            div_nonneg (mul_nonneg (by positivity) (gn0 x)) (den0 x)
  -- the Lefschetz sum
  have lefEq : b.periodicLefschetzSum s.forward s.inverse s.weight (N * m) =
      ∑ x ∈ Per, gn x / den x := by
    simp only [BasicData.periodicLefschetzSum, hn, ↓reduceDIte]
    rw [← Finset.sum_coe_sort Per]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hx : (x : M) ∈ Per := x.property
    simp only [den, gn, weightProduct, hx, ↓reduceDIte]
  have lef0 : 0 ≤ ∑ x ∈ Per, gn x / den x :=
    Finset.sum_nonneg fun x _ => div_nonneg (gn0 x) (den0 x)
  have partition : ∑ x ∈ Per, gn x / den x = ∑ i, ∑ x ∈ Per, s.cutoff i x * gn x / den x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    have sum1 := s.cutoff_sum x ((memPer x).mp hx).1
    rw [← Finset.sum_div, ← Finset.sum_mul, sum1, one_mul]
  have inner : ∑ x ∈ Per, 2 * (τ * (3 + τ)) * gn x / den x =
      2 * (τ * (3 + τ)) * ∑ x ∈ Per, gn x / den x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have constBound : card * (2 * (τ * (3 + τ))) ≤ η := by
    have τ1 : τ ≤ 1 := min_le_left _ _
    have τη : τ ≤ η / (8 * (card + 1)) := min_le_right _ _
    have h8 : 2 * (τ * (3 + τ)) ≤ 8 * τ := by nlinarith
    have hτη : 8 * τ * (card + 1) ≤ η := by
      rw [le_div_iff₀ (by positivity)] at τη
      linarith
    nlinarith
  rw [lefEq]
  change |∑ i, ∫ z, s.integrand κ (N * m) i z ∂μE - ∑ x ∈ Per, gn x / den x| ≤ _
  rw [partition, ← Finset.sum_sub_distrib]
  calc |∑ i, (∫ z, s.integrand κ (N * m) i z ∂μE - ∑ x ∈ Per, s.cutoff i x * gn x / den x)|
      ≤ ∑ i, |∫ z, s.integrand κ (N * m) i z ∂μE - ∑ x ∈ Per, s.cutoff i x * gn x / den x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : s.charts.ι, ∑ x ∈ Per, 2 * (τ * (3 + τ)) * gn x / den x :=
        Finset.sum_le_sum fun i _ => chartEstimate i
    _ = card * (2 * (τ * (3 + τ)) * ∑ x ∈ Per, gn x / den x) := by
        simp only [inner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card]
    _ = card * (2 * (τ * (3 + τ))) * ∑ x ∈ Per, gn x / den x := by ring
    _ ≤ η * ∑ x ∈ Per, gn x / den x := mul_le_mul_of_nonneg_right constBound lef0
    _ = η * ∑ i, ∑ x ∈ Per, s.cutoff i x * gn x / den x := by rw [partition]

end TraceSetup
end LeanShared.HyperbolicBasicSet
