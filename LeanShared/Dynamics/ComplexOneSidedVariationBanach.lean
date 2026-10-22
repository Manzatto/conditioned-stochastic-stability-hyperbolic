module

public import LeanShared.Dynamics.OneSidedVariationBanach
public import Mathlib.Analysis.Complex.Basic

/-! The complex Banach space of literal exponential prefix variations.
It retains the exact normalized cylinder differences and a faithful
physical realization into continuous complex functions.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
open scoped ENNReal
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A]
  {R : A → A → Prop}

abbrev ComplexVariationAmbient (R : A → A → Prop) :=
  C(FuturePath R, ℂ) × lp (fun _ : PrefixPair R => ℂ) ∞

@[expose] def complexVariationGraph (R : A → A → Prop) (θ : ℝ) :
    Submodule ℂ (ComplexVariationAmbient R) where
  carrier := {v | ∀ p : PrefixPair R,
    v.2 p * ((θ ^ p.val.1 : ℝ) : ℂ) = v.1 p.val.2.2 - v.1 p.val.2.1}
  zero_mem' := by intro p; simp
  add_mem' := by
    intro v w hv hw p
    change (v.2 p + w.2 p) * ((θ ^ p.val.1 : ℝ) : ℂ) =
      (v.1 p.val.2.2 + w.1 p.val.2.2) - (v.1 p.val.2.1 + w.1 p.val.2.1)
    rw [add_mul, hv p, hw p]
    ring
  smul_mem' := by
    intro c v hv p
    change (c * v.2 p) * ((θ ^ p.val.1 : ℝ) : ℂ) = c * v.1 p.val.2.2 - c * v.1 p.val.2.1
    rw [mul_assoc, hv p]
    ring

omit [DiscreteTopology A] [CompactSpace A] in
theorem complexVariationGraph_closed (θ : ℝ) :
    IsClosed (complexVariationGraph R θ : Set (ComplexVariationAmbient R)) := by
  change IsClosed {v : ComplexVariationAmbient R | ∀ p : PrefixPair R,
    v.2 p * ((θ ^ p.val.1 : ℝ) : ℂ) = v.1 p.val.2.2 - v.1 p.val.2.1}
  have identity : {v : ComplexVariationAmbient R | ∀ p : PrefixPair R,
      v.2 p * ((θ ^ p.val.1 : ℝ) : ℂ) = v.1 p.val.2.2 - v.1 p.val.2.1} =
      ⋂ p : PrefixPair R, {v : ComplexVariationAmbient R |
        v.2 p * ((θ ^ p.val.1 : ℝ) : ℂ) = v.1 p.val.2.2 - v.1 p.val.2.1} := by ext v; simp
  rw [identity]
  apply isClosed_iInter
  intro p
  apply isClosed_eq
  · exact ((lp.evalCLM ℂ (fun _ : PrefixPair R => ℂ) ∞ p).continuous.comp continuous_snd).mul continuous_const
  · exact ((ContinuousMap.evalCLM ℂ p.val.2.2).continuous.comp continuous_fst).sub
      ((ContinuousMap.evalCLM ℂ p.val.2.1).continuous.comp continuous_fst)

instance complexVariationGraph_complete (θ : ℝ) : CompleteSpace (complexVariationGraph R θ) :=
  (complexVariationGraph_closed θ).completeSpace_coe

@[expose] def complexVariationPhysical (θ : ℝ) :
    complexVariationGraph R θ →L[ℂ] C(FuturePath R, ℂ) :=
  (ContinuousLinearMap.fst ℂ _ _).comp (complexVariationGraph R θ).subtypeL

theorem complexVariationPhysical_norm_le (θ : ℝ) (v : complexVariationGraph R θ) :
    ‖complexVariationPhysical θ v‖ ≤ ‖v‖ := norm_fst_le v.val

omit [DiscreteTopology A] [CompactSpace A] in
theorem complexVariationPhysical_injective (θ : ℝ) (positive : 0 < θ) :
    Injective (complexVariationPhysical θ : complexVariationGraph R θ → C(FuturePath R, ℂ)) := by
  intro v w equal
  apply Subtype.ext
  apply Prod.ext
  · exact equal
  · apply lp.ext
    funext p
    apply mul_right_cancel₀ (show ((θ ^ p.val.1 : ℝ) : ℂ) ≠ 0 from
      Complex.ofReal_ne_zero.mpr (ne_of_gt (pow_pos positive p.val.1)))
    rw [v.property p, w.property p]
    change complexVariationPhysical θ v p.val.2.2 - complexVariationPhysical θ v p.val.2.1 =
      complexVariationPhysical θ w p.val.2.2 - complexVariationPhysical θ w p.val.2.1
    rw [equal]

theorem complexVariationPhysical_increment (θ : ℝ) (nonnegative : 0 ≤ θ)
    (v : complexVariationGraph R θ) (n : ℕ) (a b : FuturePath R) (same : PrefixAgreement a b n) :
    ‖complexVariationPhysical θ v b - complexVariationPhysical θ v a‖ ≤ ‖v‖ * θ ^ n := by
  let p : PrefixPair R := ⟨(n, a, b), same⟩
  have identity := v.property p
  change v.val.2 p * ((θ ^ n : ℝ) : ℂ) = complexVariationPhysical θ v b - complexVariationPhysical θ v a at identity
  rw [← identity, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg nonnegative n)]
  exact mul_le_mul_of_nonneg_right
    ((lp.norm_apply_le_norm ENNReal.top_ne_zero v.val.2 p).trans (norm_snd_le v.val))
    (pow_nonneg nonnegative n)

@[expose] def complexVariationElement (θ : ℝ) (positive : 0 < θ) (f : C(FuturePath R, ℂ))
    (C : ℝ) (_nonnegative : 0 ≤ C)
    (bound : ∀ n a b, PrefixAgreement a b n → ‖f b - f a‖ ≤ C * θ ^ n) : complexVariationGraph R θ := by
  let q : lp (fun _ : PrefixPair R => ℂ) ∞ :=
    ⟨fun p => (f p.val.2.2 - f p.val.2.1) / ((θ ^ p.val.1 : ℝ) : ℂ), memℓp_infty ⟨C, by
      rintro _ ⟨p, rfl⟩
      change ‖(f p.val.2.2 - f p.val.2.1) / ((θ ^ p.val.1 : ℝ) : ℂ)‖ ≤ C
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos positive p.val.1)]
      exact (div_le_iff₀ (pow_pos positive p.val.1)).mpr (bound _ _ _ p.property)⟩⟩
  exact ⟨(f, q), fun p => div_mul_cancel₀ _
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (pow_pos positive p.val.1)))⟩

omit [DiscreteTopology A] [CompactSpace A] in
theorem complexVariationElement_physical (θ : ℝ) (positive : 0 < θ) (f : C(FuturePath R, ℂ))
    (C : ℝ) (nonnegative : 0 ≤ C)
    (bound : ∀ n a b, PrefixAgreement a b n → ‖f b - f a‖ ≤ C * θ ^ n) :
    complexVariationPhysical θ (complexVariationElement θ positive f C nonnegative bound) = f := rfl

theorem complexVariationElement_norm_le (θ : ℝ) (positive : 0 < θ) (f : C(FuturePath R, ℂ))
    (C : ℝ) (nonnegative : 0 ≤ C)
    (bound : ∀ n a b, PrefixAgreement a b n → ‖f b - f a‖ ≤ C * θ ^ n) :
    ‖complexVariationElement θ positive f C nonnegative bound‖ ≤ max ‖f‖ C := by
  change max ‖f‖ ‖(complexVariationElement θ positive f C nonnegative bound).val.2‖ ≤ max ‖f‖ C
  apply max_le_max le_rfl
  apply lp.norm_le_of_forall_le nonnegative
  intro p
  change ‖(f p.val.2.2 - f p.val.2.1) / ((θ ^ p.val.1 : ℝ) : ℂ)‖ ≤ C
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos positive p.val.1)]
  exact (div_le_iff₀ (pow_pos positive p.val.1)).mpr (bound _ _ _ p.property)

end LeanShared.BilateralShadowingCoding
