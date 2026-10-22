module

public import LeanShared.Geometry.BoundedHolderSpace

/-! Actual Hölder lifts and little-space completions of a specified smooth
function core. Linearity follows from uniqueness of the difference quotient;
no linear choice of unrelated extensions is assumed. -/

@[expose] public noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace LeanShared.BoundedHolderSpace
variable (X : Type*) [MetricSpace X]

theorem weight_ne_zero (u : ℝ) (p : Pairs X) : weight X u p ≠ 0 := by
  unfold weight
  exact_mod_cast (Real.rpow_pos_of_pos (dist_pos.mpr p.property) u).ne'

def quotient (u : ℝ) (f : X →ᵇ ℂ) (p : Pairs X) : ℂ :=
  (f p.val.1 - f p.val.2) / weight X u p

theorem quotient_continuous (u : ℝ) (f : X →ᵇ ℂ) : Continuous (quotient X u f) := by
  have h₁ : Continuous (fun p : Pairs X => p.val.1) := continuous_fst.comp continuous_subtype_val
  have h₂ : Continuous (fun p : Pairs X => p.val.2) := continuous_snd.comp continuous_subtype_val
  have hw : Continuous (weight X u) := by
    exact Complex.continuous_ofReal.comp ((h₁.dist h₂).rpow_const
      (fun p => Or.inl (dist_pos.mpr p.property).ne'))
  exact ((f.continuous.comp h₁).sub (f.continuous.comp h₂)).div hw (weight_ne_zero X u)

theorem quotient_bound (u : ℝ) (f : X →ᵇ ℂ) (C : ℝ)
    (h : ∀ x y, ‖f x - f y‖ ≤ C * dist x y ^ u) (p : Pairs X) :
    ‖quotient X u f p‖ ≤ C := by
  have hp : 0 < dist p.val.1 p.val.2 ^ u :=
    Real.rpow_pos_of_pos (dist_pos.mpr p.property) _
  unfold quotient weight
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  exact (div_le_iff₀ hp).2 (h _ _)

def ofBound (u : ℝ) (f : X →ᵇ ℂ) (C : ℝ)
    (h : ∀ x y, ‖f x - f y‖ ≤ C * dist x y ^ u) : graph X u :=
  ⟨(f, BoundedContinuousFunction.ofNormedAddCommGroup (quotient X u f)
    (quotient_continuous X u f) C (quotient_bound X u f C h)), by
      intro p
      change quotient X u f p * weight X u p = _
      exact div_mul_cancel₀ _ (weight_ne_zero X u p)⟩

@[simp] theorem physical_ofBound (u : ℝ) (f : X →ᵇ ℂ) (C : ℝ)
    (h : ∀ x y, ‖f x - f y‖ ≤ C * dist x y ^ u) :
    physical X u (ofBound X u f C h) = f := rfl

variable {Core : Type*} [AddCommGroup Core] [Module ℂ Core]

def liftCore (u : ℝ) (f : Core →ₗ[ℂ] (X →ᵇ ℂ))
    (holder : ∀ c, ∃ C : ℝ, ∀ x y, ‖f c x - f c y‖ ≤ C * dist x y ^ u) :
    Core →ₗ[ℂ] graph X u where
  toFun c := ofBound X u (f c) (Classical.choose (holder c)) (Classical.choose_spec (holder c))
  map_add' c d := by
    apply physical_injective X u
    change f (c + d) = physical X u (_ + _)
    rw [(physical X u).map_add]
    exact f.map_add c d
  map_smul' a c := by
    apply physical_injective X u
    change f (a • c) = physical X u (a • _)
    rw [(physical X u).map_smul]
    exact f.map_smul a c

@[simp] theorem physical_liftCore (u : ℝ) (f : Core →ₗ[ℂ] (X →ᵇ ℂ))
    (holder : ∀ c, ∃ C : ℝ, ∀ x y, ‖f c x - f c y‖ ≤ C * dist x y ^ u) (c : Core) :
    physical X u (liftCore X u f holder c) = f c := rfl

def corePhysical (u : ℝ) (f : Core →ₗ[ℂ] (X →ᵇ ℂ))
    (holder : ∀ c, ∃ C : ℝ, ∀ x y, ‖f c x - f c y‖ ≤ C * dist x y ^ u) :
    DyadicCompletion.closedCore (liftCore X u f holder) →L[ℂ] (X →ᵇ ℂ) :=
  (physical X u).comp (DyadicCompletion.closedCore (liftCore X u f holder)).subtypeL

theorem corePhysical_injective (u : ℝ) (f : Core →ₗ[ℂ] (X →ᵇ ℂ))
    (holder : ∀ c, ∃ C : ℝ, ∀ x y, ‖f c x - f c y‖ ≤ C * dist x y ^ u) :
    Function.Injective (corePhysical X u f holder) :=
  (physical_injective X u).comp Subtype.val_injective

theorem corePhysical_zero_outside (u : ℝ) (f : Core →ₗ[ℂ] (X →ᵇ ℂ))
    (holder : ∀ c, ∃ C : ℝ, ∀ x y, ‖f c x - f c y‖ ≤ C * dist x y ^ u)
    (V : Set X) (supported : ∀ c x, x ∉ V → f c x = 0)
    (v : DyadicCompletion.closedCore (liftCore X u f holder)) (x : X) (hx : x ∉ V) :
    corePhysical X u f holder v x = 0 := by
  apply (DyadicCompletion.coreLift_dense (liftCore X u f holder)).induction_on
    (p := fun z => corePhysical X u f holder z x = 0) v
    (isClosed_eq ((BoundedContinuousFunction.evalCLM ℂ x).continuous.comp
      (corePhysical X u f holder).continuous) continuous_const)
  intro c
  exact supported c x hx

end LeanShared.BoundedHolderSpace
