module
public import LeanShared.Dynamics.PeriodicChainDeterminant
public import LeanShared.Dynamics.LocalPeriodicIntegral

/-! The local regularized trace at one periodic orbit, in the chart of a periodic chain.
Lebesgue measure on the chart is pulled back by the affine chart normalization
`z ↦ L_0⁻¹(z - a_0)`, a Haar measure on `U × S`. On the region of the chain data the chart
integrand `G(φ_i⁻¹ z) κ_ε(φ_i(H^m(φ_i⁻¹ z)) - z)` becomes `G(decode w) κ_ε(L_0 F(w))`, and the
uniform local periodic integral estimate gives `G(p)/|det(1 - P_0)|` up to
`2 (η_G + c (bound ε)^α |G p|)/|det(1 - P_0)|`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Bundle Metric MeasureTheory
open scoped Manifold ContDiff Topology NNReal
open LeanShared.HyperbolicBasicSet LeanShared.PeriodicChartConstants
namespace LeanShared.PeriodicChartChains

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}
  {a : IsometricFraming h} {F : ChartFamily E M} {H : M → M} {lam : ℝ}

namespace PeriodicChain

variable {p : Λ} {m : ℕ} {i : F.ι} (pc : PeriodicChain a F H lam p m i)

/-- The affine chart normalization at the base point. -/
@[expose] def affine : E ≃ₜ (EuclideanSpace ℝ (Fin a.unstableDimension) ×
    EuclideanSpace ℝ (Fin a.stableDimension)) :=
  (Homeomorph.addRight (-pc.chain.a 0)).trans (pc.chain.L 0).symm.toHomeomorph

omit [MeasurableSpace E] [BorelSpace E] in
theorem affine_apply (z : E) : pc.affine z = (pc.chain.L 0).symm (z - pc.chain.a 0) := by
  simp only [affine, Homeomorph.trans_apply, Homeomorph.coe_addRight, sub_eq_add_neg]
  rfl

/-- The pulled back Haar measure. -/
@[expose] def pulled (μE : Measure E) : Measure (EuclideanSpace ℝ (Fin a.unstableDimension) ×
    EuclideanSpace ℝ (Fin a.stableDimension)) := Measure.map pc.affine μE

theorem pulled_eq (μE : Measure E) [μE.IsAddHaarMeasure] :
    pc.pulled μE = Measure.map (pc.chain.L 0).symm μE := by
  have split : (pc.affine : E → _) = (pc.chain.L 0).symm ∘ (fun z => z + -pc.chain.a 0) := by
    funext z
    rw [affine_apply, sub_eq_add_neg]
    rfl
  rw [pulled, split, ← Measure.map_map (pc.chain.L 0).symm.continuous.measurable
    (measurable_add_const _), map_add_right_eq_self]

instance pulled_haar (μE : Measure E) [μE.IsAddHaarMeasure] : (pc.pulled μE).IsAddHaarMeasure := by
  rw [pc.pulled_eq μE]
  infer_instance

omit [MeasurableSpace E] [BorelSpace E] in
theorem decode_zero : pc.decode 0 = p.val := by
  simp only [decode, map_zero, add_zero]
  have source := pc.source_point 0
  rw [pc.σ_zero, pc.point_zero] at source
  rw [pc.a_eq 0, pc.σ_zero, pc.point_zero]
  exact (F.chart i).left_inv source

omit [MeasurableSpace E] [BorelSpace E] in
theorem decode_continuousOn (δD : ℝ≥0) (hδD : 0 < δD) (small : pc.chain.k + δD * 2 < 1) :
    ContinuousOn pc.decode (pc.chain.toData δD hδD small).region := by
  intro w hw
  have hr := pc.chain.radius_pos δD hδD
  have hw0 : ‖w‖ ≤ 2 * pc.chain.radius δD := by
    have := hw 0 (Nat.zero_le _)
    change ‖w‖ ≤ pc.chain.radius δD at this
    linarith
  have target : pc.chain.a 0 + pc.chain.L 0 w ∈ (F.chart i).target := by
    have mem := pc.chart_symm_mem 0 _ (pc.ball_of_radius δD 0 w hw0)
    rw [pc.σ_zero] at mem
    rw [← mem.2]
    exact (F.chart i).map_source mem.1
  have affineC : Continuous (fun v : EuclideanSpace ℝ (Fin a.unstableDimension) ×
      EuclideanSpace ℝ (Fin a.stableDimension) => pc.chain.a 0 + pc.chain.L 0 v) :=
    continuous_const.add (pc.chain.L 0).continuous
  change ContinuousWithinAt ((F.chart i).symm ∘ fun v => pc.chain.a 0 + pc.chain.L 0 v) _ w
  exact ContinuousAt.comp_continuousWithinAt (((F.chart i).continuousOn_symm.continuousAt
    ((F.chart i).open_target.mem_nhds target))) affineC.continuousWithinAt

end PeriodicChain

/-- The uniform local regularized trace estimate at periodic orbits. -/
theorem exists_local_estimate (k δD : ℝ≥0) (hδD : 0 < δD) (small : k + δD * 2 < 1)
    (K α : ℝ) (hK : 0 ≤ K) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ c ρ1 : ℝ, 0 < c ∧ 0 < ρ1 ∧ ∀ {p : Λ} {m : ℕ} {i : F.ι} (pc : PeriodicChain a F H lam p m i)
      (small' : pc.chain.k + δD * 2 < 1), pc.chain.k = k → pc.chain.holderK = K →
      pc.chain.α = α →
      ∀ (μE : Measure E) [μE.IsAddHaarMeasure] (κ : E → ℝ), Continuous κ → (∀ z, 0 ≤ κ z) →
      HasCompactSupport κ → ∀ ε : ℝ, 0 < ε → (∀ z, ε < ‖z‖ → κ z = 0) → ∫ z, κ z ∂μE = 1 →
      pc.chain.bound * ε ≤ ρ1 →
      ((pc.chain.toData δD hδD small').constant + 1) * (pc.chain.bound * ε) ≤
        (pc.chain.toData δD hδD small').r →
      ∀ G : M → ℝ, Continuous G → ∀ ηG : ℝ,
      (∀ w ∈ (pc.chain.toData δD hδD small').region,
        ‖(pc.chain.toData δD hδD small').closing w‖ ≤ pc.chain.bound * ε →
        |G (pc.decode w) - G p.val| ≤ ηG) →
      abs (∫ z in pc.affine ⁻¹' (pc.chain.toData δD hδD small').region,
          G ((F.chart i).symm z) * κ (F.chart i (H^[m] ((F.chart i).symm z)) - z) ∂μE -
        G p.val / abs (LinearMap.det ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin a.unstableDimension) ×
            EuclideanSpace ℝ (Fin a.stableDimension)) - CyclicHyperbolicDeterminant.prodFrom
          (pc.chain.toData δD hδD small').D 0 (pc.chain.toData δD hδD small').period) :
            (EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
              →ₗ[ℝ] _))) ≤
        2 * (ηG + c * (pc.chain.bound * ε) ^ α * abs (G p.val)) /
          abs (LinearMap.det ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin a.unstableDimension) ×
            EuclideanSpace ℝ (Fin a.stableDimension)) - CyclicHyperbolicDeterminant.prodFrom
          (pc.chain.toData δD hδD small').D 0 (pc.chain.toData δD hδD small').period) :
            (EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
              →ₗ[ℝ] _)) := by
  obtain ⟨c, ρ1, hc, hρ1, est⟩ := LocalPeriodicClosing.Data.integral_estimate
    (U := EuclideanSpace ℝ (Fin a.unstableDimension)) (S := EuclideanSpace ℝ (Fin a.stableDimension))
    k δD small K α hK hα hα1
  refine ⟨c, ρ1, hc, hρ1, ?_⟩
  intro p m i pc small' hk hK' hα' μE _ κ hκ hκ0 hκc ε hε support mass hρ hρr G hG ηG close
  set d := pc.chain.toData δD hδD small'
  have holder : ∀ j v, ‖v‖ ≤ d.r → ‖d.H' j v - d.D j‖ ≤ K * ‖v‖ ^ α := by
    intro j v hv
    have := pc.chain.toData_holder δD hδD small' j v hv
    rwa [hK', hα'] at this
  set ν := pc.pulled μE
  set L0 := pc.chain.L 0
  set κhat : EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension) → ℝ :=
    fun b => κ (L0 b)
  have κhatC : Continuous κhat := hκ.comp L0.continuous
  have κhat0 : ∀ b, 0 ≤ κhat b := fun b => hκ0 _
  have κhatSupport : HasCompactSupport κhat := hκc.comp_homeomorph L0.toHomeomorph
  have κhatBall : ∀ b, pc.chain.bound * ε < ‖b‖ → κhat b = 0 := by
    intro b hb
    apply support
    by_contra hle
    push Not at hle
    have : ‖b‖ ≤ pc.chain.bound * ‖L0 b‖ := by
      calc ‖b‖ = ‖L0.symm (L0 b)‖ := by rw [ContinuousLinearEquiv.symm_apply_apply]
        _ ≤ ‖L0.symm.toContinuousLinearMap‖ * ‖L0 b‖ := L0.symm.toContinuousLinearMap.le_opNorm _
        _ ≤ pc.chain.bound * ‖L0 b‖ :=
            mul_le_mul_of_nonneg_right (pc.chain.L_inv_bound 0) (norm_nonneg _)
    have hb' := pc.chain.bound_pos
    nlinarith
  have κhatMass : ∫ b, κhat b ∂ν = 1 := by
    simp only [ν, PeriodicChain.pulled, κhat]
    change ∫ b, (κ ∘ L0) b ∂(Measure.map pc.affine μE) = 1
    rw [integral_map pc.affine.continuous.measurable.aemeasurable
      (hκ.comp L0.continuous).aestronglyMeasurable]
    have shift (z : E) : L0 (pc.affine z) = z - pc.chain.a 0 := by
      rw [PeriodicChain.affine_apply, ContinuousLinearEquiv.apply_symm_apply]
    simp only [Function.comp_apply, shift]
    rw [integral_sub_right_eq_self (fun z => κ z) (pc.chain.a 0)]
    exact mass
  set Gw : EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension) → ℝ :=
    fun w => G (pc.decode w)
  have GwC : ContinuousOn Gw d.region := hG.comp_continuousOn (pc.decode_continuousOn δD hδD small')
  have closeW : ∀ w ∈ d.region, ‖d.closing w‖ ≤ pc.chain.bound * ε → |Gw w - Gw 0| ≤ ηG := by
    intro w hw hb
    simp only [Gw, pc.decode_zero]
    exact close w hw hb
  have main := est d hk rfl holder ν κhat κhatC κhat0 κhatSupport (pc.chain.bound * ε)
    (by have := pc.chain.bound_pos; positivity) hρ hρr κhatBall Gw GwC ηG closeW
  rw [κhatMass, mul_one, mul_one] at main
  simp only [Gw, pc.decode_zero] at main
  -- identify the pulled back integral with the chart integral
  have identify : ∫ w in d.region, G (pc.decode w) * κhat (d.closing w) ∂ν =
      ∫ z in pc.affine ⁻¹' d.region,
        G ((F.chart i).symm z) * κ (F.chart i (H^[m] ((F.chart i).symm z)) - z) ∂μE := by
    simp only [ν, PeriodicChain.pulled]
    rw [show Measure.map (pc.affine : E → _) μE = Measure.map (pc.affine.toMeasurableEquiv) μE from rfl,
      setIntegral_map_equiv pc.affine.toMeasurableEquiv]
    refine setIntegral_congr_fun ((d.isClosed_region.preimage pc.affine.continuous).measurableSet)
      fun z hz => ?_
    change pc.affine z ∈ d.region at hz
    have decodeEq : pc.decode (pc.affine z) = (F.chart i).symm z := by
      simp only [PeriodicChain.decode, PeriodicChain.affine_apply,
        ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
    have hr := pc.chain.radius_pos δD hδD
    have hz0 : ‖pc.affine z‖ ≤ 2 * pc.chain.radius δD := by
      have := hz 0 (Nat.zero_le _)
      change ‖pc.affine z‖ ≤ pc.chain.radius δD at this
      linarith
    have chartEq : F.chart i ((F.chart i).symm z) = z := by
      have mem := pc.chart_symm_mem 0 _ (pc.ball_of_radius δD 0 _ hz0)
      rw [pc.σ_zero] at mem
      have eq2 := mem.2
      simp only [PeriodicChain.affine_apply, ContinuousLinearEquiv.apply_symm_apply,
        add_sub_cancel] at eq2
      exact eq2
    change G (pc.decode (pc.affine z)) * κ (L0 (d.closing (pc.affine z))) = _
    rw [pc.closing_eq δD hδD small' _ hz, ContinuousLinearEquiv.apply_symm_apply, decodeEq,
      chartEq]
  rw [identify] at main
  exact main

end LeanShared.PeriodicChartChains
