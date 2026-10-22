module

public import ConditionedStochasticStabilityHyperbolic.Restriction.SupportedRestriction
public import ConditionedStochasticStabilityHyperbolic.Restriction.FiniteLifting

/-! # Restriction of powers applied to harmonic-weighted observables

Positivity dominates each iterated product by the nonnegative harmonic
function. No-return exits into its zero region therefore contribute nothing,
so full and retained powers agree on the products used by QEM pairings.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Restriction

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

omit [OpensMeasurableSpace X] in
theorem restrict_power_of_bad_region_vanishing
    (K : Kernel X X) (V B : Set X) (hV : MeasurableSet V)
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (Q : (V →ᵇ ℝ) →L[ℝ] (V →ᵇ ℝ))
    (hP : ∀ (f : X →ᵇ ℝ) (x : X), P f x = ∫ y, f y ∂K x)
    (hQ : ∀ (f : V →ᵇ ℝ) (x : V), Q f x =
      ∫ y, f y ∂LeanShared.SubtypeKernel.restrict K V hV x)
    (hreturn : ∀ x : V, ∀ᵐ y ∂K x.val, y ∉ V → y ∈ B)
    (u : X →ᵇ ℝ) (hzero : ∀ n, ∀ x ∈ B, (P ^ n) u x = 0) (n : ℕ) :
    restrictObservable V ((P ^ n) u) = (Q ^ n) (restrictObservable V u) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, ← ih]
      ext x
      rw [restrictObservable_apply, hP, hQ]
      symm
      apply integral_subtype_of_ae_outside_zero K V hV _ x
      filter_upwards [hreturn x] with y hy hout
      exact hzero n y (hy hout)

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem positive_operator_monotone
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (hpos : ∀ f, 0 ≤ f → 0 ≤ P f) :
    Monotone P := by
  intro u v huv
  have h := hpos (v - u) (sub_nonneg.mpr huv)
  rw [map_sub] at h
  exact sub_nonneg.mp h

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem harmonic_product_power_bounds
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (hpos : ∀ f, 0 ≤ f → 0 ≤ P f)
    (g h : X →ᵇ ℝ) (hg : 0 ≤ g) (r : ℝ)
    (heig : P g = r • g) (n : ℕ) :
    (-(‖h‖ * r ^ n)) • g ≤ (P ^ n) (g * h) ∧
      (P ^ n) (g * h) ≤ (‖h‖ * r ^ n) • g := by
  have hmono := positive_operator_monotone P hpos
  induction n with
  | zero =>
      simp only [pow_zero, mul_one, one_apply_eq_self]
      constructor <;> intro x
      · change -‖h‖ * g x ≤ g x * h x
        have hh : -‖h‖ ≤ h x := by
          have hn := h.norm_coe_le_norm x
          rw [Real.norm_eq_abs] at hn
          exact (abs_le.mp hn).1
        have hmul := mul_le_mul_of_nonneg_left hh (hg x)
        rw [mul_comm] at hmul
        exact hmul
      · change g x * h x ≤ ‖h‖ * g x
        have hh : h x ≤ ‖h‖ := by
          have hn := h.norm_coe_le_norm x
          rw [Real.norm_eq_abs] at hn
          exact (abs_le.mp hn).2
        have hmul := mul_le_mul_of_nonneg_left hh (hg x)
        rw [mul_comm _ ‖h‖] at hmul
        exact hmul
  | succ n ih =>
      rw [show P ^ (n + 1) = P * P ^ n from pow_succ' P n, mul_apply_eq_comp]
      have hlo := hmono ih.1
      have hhi := hmono ih.2
      rw [map_smul, heig, smul_smul] at hlo hhi
      constructor
      · convert hlo using 1
        congr 1
        ring
      · convert hhi using 1
        congr 1
        ring

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem harmonic_product_power_vanishes
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (hpos : ∀ f, 0 ≤ f → 0 ≤ P f)
    (g h : X →ᵇ ℝ) (hg : 0 ≤ g) (r : ℝ)
    (heig : P g = r • g) (B : Set X) (hB : ∀ x ∈ B, g x = 0) :
    ∀ n, ∀ x ∈ B, (P ^ n) (g * h) x = 0 := by
  intro n x hx
  obtain ⟨hlo, hhi⟩ := harmonic_product_power_bounds P hpos g h hg r heig n
  apply le_antisymm
  · simpa [hB x hx] using hhi x
  · simpa [hB x hx] using hlo x

omit [OpensMeasurableSpace X] in
theorem restrict_harmonic_product_power
    (K : Kernel X X) (V B : Set X) (hV : MeasurableSet V)
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (Q : (V →ᵇ ℝ) →L[ℝ] (V →ᵇ ℝ))
    (hP : ∀ (f : X →ᵇ ℝ) (x : X), P f x = ∫ y, f y ∂K x)
    (hQ : ∀ (f : V →ᵇ ℝ) (x : V), Q f x =
      ∫ y, f y ∂LeanShared.SubtypeKernel.restrict K V hV x)
    (hreturn : ∀ x : V, ∀ᵐ y ∂K x.val, y ∉ V → y ∈ B)
    (hpos : ∀ f, 0 ≤ f → 0 ≤ P f)
    (g h : X →ᵇ ℝ) (hg : 0 ≤ g) (r : ℝ)
    (heig : P g = r • g) (hB : ∀ x ∈ B, g x = 0) (n : ℕ) :
    restrictObservable V ((P ^ n) (g * h)) =
      (Q ^ n) (restrictObservable V g * restrictObservable V h) := by
  have hm : restrictObservable V (g * h) = restrictObservable V g * restrictObservable V h := rfl
  rw [← hm]
  exact restrict_power_of_bad_region_vanishing K V B hV P Q hP hQ hreturn _
    (harmonic_product_power_vanishes P hpos g h hg r heig B hB) n

/-- For the actual canonical chain, positivity and harmonic vanishing are
derived from its kernel and finite extinction. -/
theorem restrict_actual_harmonic_product_power
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (V B : Set X) (hV : MeasurableSet V)
    (hreturn : ∀ x : V, ∀ᵐ y ∂C.killedTransition x.val, y ∉ V → y ∈ B)
    (hext : ∀ x ∈ B, ∃ n : ℕ,
      C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (g h : X →ᵇ ℝ) (hg : 0 ≤ g) (r : ℝ) (hr : r ≠ 0)
    (heig : ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF g = r • g) (n : ℕ) :
    restrictObservable V ((ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF ^ n) (g * h)) =
      (smoothedSubtypeTransfer (𝕜 := ℝ) C hSF V hV ^ n)
        (restrictObservable V g * restrictObservable V h) := by
  have hpos : ∀ f : X →ᵇ ℝ, 0 ≤ f →
      0 ≤ ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF f := by
    intro f hf x
    change 0 ≤ ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF f x
    rw [ComplexStrongFeller.transferOperator_apply]
    exact integral_nonneg (fun y => hf y)
  have hB : ∀ x ∈ B, g x = 0 := by
    intro x hx
    obtain ⟨N, hN⟩ := hext x hx
    exact eigenfunction_vanishes_of_finite_extinction C
      (ComplexStrongFeller.transferOperator C hSF)
      (ComplexStrongFeller.transferOperator_apply C hSF) hr g heig x N hN
  exact restrict_harmonic_product_power C.killedTransition V B hV
    (ComplexStrongFeller.transferOperator C hSF) (smoothedSubtypeTransfer C hSF V hV)
    (ComplexStrongFeller.transferOperator_apply C hSF)
    (smoothedSubtypeTransfer_represents C hSF V hV) hreturn hpos g h hg r heig hB n

end ConditionedStochasticStabilityHyperbolic.Restriction
