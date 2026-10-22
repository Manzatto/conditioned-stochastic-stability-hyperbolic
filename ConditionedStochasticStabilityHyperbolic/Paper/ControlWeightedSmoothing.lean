module

public import ConditionedStochasticStabilityHyperbolic.Paper.SmoothSubmersionSource
public import LeanShared.Probability.StateWeightedSmoothing

/-! The same unweighted smooth-density submersion source also yields the
inverse operator's state-and-noise Jacobian smoothing. Freeze its weight,
absorb it in an L¹ control density, and use dominated convergence for the
remaining state variation. No noise derivative of that Jacobian is assumed. -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared WeightedNoiseL1Approximation
variable {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [Fintype ι]

/-- An arbitrary bounded measurable control weight is absorbed into the
actual L¹ law density, rather than differentiated. -/
theorem Laws.continuous_control_weighted_integral
    (L : Laws (ι := ι)) (ε : ℝ≥0) (hε : 0 < ε)
    (H : X × cube (ι := ι) ε → X) (hH : Measurable H)
    (b : cube (ι := ι) ε → ℝ) (hb : Measurable b) (B : ℝ)
    (bound : ∀ z, ‖b z‖ ≤ B)
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (fbound : ∀ x, ‖f x‖ ≤ C)
    (smoothSource : ∀ g : Control (ι := ι) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
      Continuous (fun x => ∫ z : cube (ι := ι) ε, g z.val * f (H (x, z)) ∂cubeVolume ε)) :
    Continuous (fun x => ∫ z, b z * f (H (x, z)) ∂L.law ε) := by
  obtain ⟨p, hp, hp0, hpi, _, hrepr⟩ := L.exists_real_integrable_density ε hε
  have hpb : Integrable (fun z => p z * b z) (cubeVolume ε) :=
    hpi.mul_bdd hb.aestronglyMeasurable (ae_of_all _ bound)
  obtain ⟨pn, hpn, hlim⟩ := exists_smooth_cube_approximation ε (fun z => p z * b z) hpb
  have hc := continuous_weighted_integral_of_L1_approximation (cubeVolume ε)
    (fun z => p z * b z) hpb (fun n z => pn n z.val) (fun n => (hpn n).2.2) hlim
    H hH (fun _ => (1 : ℝ)) measurable_const 1 zero_le_one (fun _ _ => by simp)
    f hf C hC fbound
    (fun n => by simpa only [one_mul] using smoothSource (pn n) (hpn n).1 (hpn n).2.1)
  have heq (x : X) : (∫ z, b z * f (H (x, z)) ∂L.law ε) =
      ∫ z, (p z * b z) * (1 * f (H (x, z))) ∂cubeVolume ε := by
    rw [hrepr, integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hp0 _), smul_eq_mul, one_mul, mul_assoc]
  exact hc.congr (fun x => (heq x).symm)

/-- Full state-and-control weights need only be measurable, bounded and
continuous in the state; the ordinary rank source remains unweighted. -/
theorem Laws.continuous_state_control_weighted_integral [FirstCountableTopology X]
    (L : Laws (ι := ι)) (ε : ℝ≥0) (hε : 0 < ε)
    (H : X × cube (ι := ι) ε → X) (hH : Measurable H)
    (W : X × cube (ι := ι) ε → ℝ) (hW : Measurable W)
    (weight_continuous : ∀ z, Continuous (fun x => W (x, z)))
    (B : ℝ) (hB : 0 ≤ B) (bound : ∀ x z, ‖W (x, z)‖ ≤ B)
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (fbound : ∀ x, ‖f x‖ ≤ C)
    (smoothSource : ∀ g : Control (ι := ι) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
      Continuous (fun x => ∫ z : cube (ι := ι) ε, g z.val * f (H (x, z)) ∂cubeVolume ε)) :
    Continuous (fun x => ∫ z, W (x, z) * f (H (x, z)) ∂L.law ε) :=
  StateWeightedSmoothing.continuous_weighted_integral (L.law ε) H hH W hW
    weight_continuous B hB bound f hf C hC fbound
    (fun b hb hbB => L.continuous_control_weighted_integral ε hε H hH b hb B hbB
      f hf C hC fbound smoothSource)


/-- Killing at a measurable region preserves the derived weighted smoothing.
The observable is extended by an indicator; no regularity of the boundary is
used. -/
theorem Laws.continuous_weighted_killed_from_unweighted_source [FirstCountableTopology X]
    (L : Laws (ι := ι)) (ε : ℝ≥0) (hε : 0 < ε)
    (H : X × cube (ι := ι) ε → X) (hH : Measurable H)
    (W : X × cube (ι := ι) ε → ℝ) (hW : Measurable W)
    (hW0 : ∀ x z, 0 ≤ W (x, z))
    (weight_continuous : ∀ z, Continuous (fun x => W (x, z)))
    (B : ℝ) (hB : 0 ≤ B) (bound : ∀ x z, ‖W (x, z)‖ ≤ B)
    (K : Set X) (hK : MeasurableSet K)
    (smoothSource : ∀ g : Control (ι := ι) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
      ∀ f : X → ℝ, Measurable f → (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C) →
        Continuous (fun x => ∫ z : cube (ι := ι) ε, g z.val * f (H (x, z)) ∂cubeVolume ε))
    (f : X → ℝ) (hf : Measurable f)
    (fb : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C) :
    Continuous (fun x => ∫ y, f y ∂WeightedRandomMapKernel.killed (L.law ε) W H K hK x) := by
  obtain ⟨C, hC, hb⟩ := fb
  have hib (x : X) : ‖K.indicator f x‖ ≤ C := by
    by_cases hx : x ∈ K
    · simpa only [indicator_of_mem hx] using hb x
    · simpa only [indicator_of_notMem hx, norm_zero] using hC
  have hc := L.continuous_state_control_weighted_integral ε hε H hH W hW
    weight_continuous B hB bound (K.indicator f) (hf.indicator hK) C hC hib
    (fun g hg hs => smoothSource g hg hs (K.indicator f) (hf.indicator hK) ⟨C, hC, hib⟩)
  exact hc.congr (fun x => (WeightedRandomMapKernel.integral_killed (L.law ε) W hW
    H hH hW0 K hK f hf x).symm)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
