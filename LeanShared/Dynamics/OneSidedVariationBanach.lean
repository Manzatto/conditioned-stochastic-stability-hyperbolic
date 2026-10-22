module

public import LeanShared.Dynamics.OneSidedExponentialPotential
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-! A concrete Banach space for a fixed exponential prefix rate, realized
as the closed graph of all literal normalized cylinder differences.
Its norm controls both the uniform norm and every prefix difference.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
open scoped ENNReal
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A]
  {R : A → A → Prop}

@[expose] def PrefixPair (R : A → A → Prop) :=
  {p : ℕ × (FuturePath R × FuturePath R) // PrefixAgreement p.2.1 p.2.2 p.1}

abbrev VariationAmbient (R : A → A → Prop) :=
  C(FuturePath R, ℝ) × lp (fun _ : PrefixPair R => ℝ) ∞

@[expose] def variationGraph (R : A → A → Prop) (θ : ℝ) : Submodule ℝ (VariationAmbient R) where
  carrier := {v | ∀ p : PrefixPair R,
    v.2 p * θ ^ p.val.1 = v.1 p.val.2.2 - v.1 p.val.2.1}
  zero_mem' := by intro p; simp
  add_mem' := by
    intro v w hv hw p
    change (v.2 p + w.2 p) * θ ^ p.val.1 =
      (v.1 p.val.2.2 + w.1 p.val.2.2) - (v.1 p.val.2.1 + w.1 p.val.2.1)
    rw [add_mul, hv p, hw p]
    ring
  smul_mem' := by
    intro c v hv p
    change (c * v.2 p) * θ ^ p.val.1 = c * v.1 p.val.2.2 - c * v.1 p.val.2.1
    rw [mul_assoc, hv p]
    ring

omit [DiscreteTopology A] [CompactSpace A] in
theorem variationGraph_closed (θ : ℝ) : IsClosed (variationGraph R θ : Set (VariationAmbient R)) := by
  change IsClosed {v : VariationAmbient R | ∀ p : PrefixPair R,
    v.2 p * θ ^ p.val.1 = v.1 p.val.2.2 - v.1 p.val.2.1}
  have identity : {v : VariationAmbient R | ∀ p : PrefixPair R,
      v.2 p * θ ^ p.val.1 = v.1 p.val.2.2 - v.1 p.val.2.1} =
      ⋂ p : PrefixPair R, {v : VariationAmbient R |
        v.2 p * θ ^ p.val.1 = v.1 p.val.2.2 - v.1 p.val.2.1} := by ext v; simp
  rw [identity]
  apply isClosed_iInter
  intro p
  apply isClosed_eq
  · exact ((lp.evalCLM ℝ (fun _ : PrefixPair R => ℝ) ∞ p).continuous.comp continuous_snd).mul continuous_const
  · exact ((ContinuousMap.evalCLM ℝ p.val.2.2).continuous.comp continuous_fst).sub
      ((ContinuousMap.evalCLM ℝ p.val.2.1).continuous.comp continuous_fst)

instance variationGraph_complete (θ : ℝ) : CompleteSpace (variationGraph R θ) :=
  (variationGraph_closed θ).completeSpace_coe

@[expose] def variationPhysical (θ : ℝ) : variationGraph R θ →L[ℝ] C(FuturePath R, ℝ) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (variationGraph R θ).subtypeL

theorem variationPhysical_norm_le (θ : ℝ) (v : variationGraph R θ) :
    ‖variationPhysical θ v‖ ≤ ‖v‖ := norm_fst_le v.val

omit [DiscreteTopology A] [CompactSpace A] in
theorem variationPhysical_injective (θ : ℝ) (positive : 0 < θ) :
    Injective (variationPhysical θ : variationGraph R θ → C(FuturePath R, ℝ)) := by
  intro v w equal
  apply Subtype.ext
  apply Prod.ext
  · exact equal
  · apply lp.ext
    funext p
    apply mul_right_cancel₀ (ne_of_gt (pow_pos positive p.val.1))
    rw [v.property p, w.property p]
    change (variationPhysical θ v) p.val.2.2 - (variationPhysical θ v) p.val.2.1 =
      (variationPhysical θ w) p.val.2.2 - (variationPhysical θ w) p.val.2.1
    rw [equal]

theorem variationPhysical_increment (θ : ℝ) (nonnegative : 0 ≤ θ)
    (v : variationGraph R θ) (n : ℕ) (a b : FuturePath R) (same : PrefixAgreement a b n) :
    |variationPhysical θ v b - variationPhysical θ v a| ≤ ‖v‖ * θ ^ n := by
  let p : PrefixPair R := ⟨(n, a, b), same⟩
  have identity := v.property p
  change v.val.2 p * θ ^ n = (variationPhysical θ v) b - (variationPhysical θ v) a at identity
  rw [← identity, abs_mul, abs_of_nonneg (pow_nonneg nonnegative n)]
  exact mul_le_mul_of_nonneg_right
    ((lp.norm_apply_le_norm ENNReal.top_ne_zero v.val.2 p).trans (norm_snd_le v.val))
    (pow_nonneg nonnegative n)

@[expose] def variationElement (θ : ℝ) (positive : 0 < θ) (f : C(FuturePath R, ℝ))
    (C : ℝ) (_nonnegative : 0 ≤ C)
    (bound : ∀ n a b, PrefixAgreement a b n → |f b - f a| ≤ C * θ ^ n) : variationGraph R θ := by
  let q : lp (fun _ : PrefixPair R => ℝ) ∞ :=
    ⟨fun p => (f p.val.2.2 - f p.val.2.1) / θ ^ p.val.1, memℓp_infty ⟨C, by
      rintro _ ⟨p, rfl⟩
      change ‖(f p.val.2.2 - f p.val.2.1) / θ ^ p.val.1‖ ≤ C
      simp only [norm_div, Real.norm_eq_abs, abs_of_pos (pow_pos positive p.val.1)]
      exact (div_le_iff₀ (pow_pos positive p.val.1)).mpr (bound _ _ _ p.property)⟩⟩
  exact ⟨(f, q), fun p => div_mul_cancel₀ _ (ne_of_gt (pow_pos positive p.val.1))⟩

omit [DiscreteTopology A] [CompactSpace A] in
theorem variationElement_physical (θ : ℝ) (positive : 0 < θ) (f : C(FuturePath R, ℝ))
    (C : ℝ) (nonnegative : 0 ≤ C)
    (bound : ∀ n a b, PrefixAgreement a b n → |f b - f a| ≤ C * θ ^ n) :
    variationPhysical θ (variationElement θ positive f C nonnegative bound) = f := rfl

theorem variationElement_norm_le (θ : ℝ) (positive : 0 < θ) (f : C(FuturePath R, ℝ))
    (C : ℝ) (nonnegative : 0 ≤ C)
    (bound : ∀ n a b, PrefixAgreement a b n → |f b - f a| ≤ C * θ ^ n) :
    ‖variationElement θ positive f C nonnegative bound‖ ≤ max ‖f‖ C := by
  change max ‖f‖ ‖(variationElement θ positive f C nonnegative bound).val.2‖ ≤ max ‖f‖ C
  apply max_le_max le_rfl
  apply lp.norm_le_of_forall_le nonnegative
  intro p
  change ‖(f p.val.2.2 - f p.val.2.1) / θ ^ p.val.1‖ ≤ C
  simp only [norm_div, Real.norm_eq_abs, abs_of_pos (pow_pos positive p.val.1)]
  exact (div_le_iff₀ (pow_pos positive p.val.1)).mpr (bound _ _ _ p.property)

end LeanShared.BilateralShadowingCoding
