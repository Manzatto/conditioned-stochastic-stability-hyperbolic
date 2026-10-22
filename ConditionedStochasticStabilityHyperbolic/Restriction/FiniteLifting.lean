module

public import ConditionedStochasticStabilityHyperbolic.Restriction.SupportedRestriction
public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexStrongFeller

/-!
# Actual-kernel first-entrance extinction and finite lifting

Finite extinction of the full killed chain annihilates first-entrance
functionals on every nonzero generalized eigenspace of its subtype transfer.
This controls exits from the retained region without assuming the bad region
is invariant or that zero extension preserves continuity.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Restriction

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {𝕜 : Type*} [RCLike 𝕜]

section Extinction

variable (C : AbsorbingMarkovChains.CanonicalChain X)

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- Finite extinction propagates to almost every live successor at the
same horizon, by monotonicity of survival and positivity of kernel composition. -/
theorem ae_extinction_successor (N : ℕ) (x : X)
    (hx : (C.killedTransition ^ N) x univ = 0) :
    ∀ᵐ y ∂C.killedTransition x, (C.killedTransition ^ N) y univ = 0 := by
  have hn : (C.killedTransition ^ (N + 1)) x univ = 0 := by
    rw [← C.pathMeasure_survival] at hx ⊢
    exact measure_mono_null (AbsorbingMarkovChains.CanonicalChain.survival_antitone
      (Nat.le_succ N)) hx
  rw [Kernel.pow_add, pow_one] at hn
  exact Kernel.ae_null_of_comp_null hn

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- The preceding, shorter horizon propagates under a zero successor law. -/
theorem ae_extinction_predecessor (N : ℕ) (x : X)
    (hx : (C.killedTransition ^ (N + 1)) x univ = 0) :
    ∀ᵐ y ∂C.killedTransition x, (C.killedTransition ^ N) y univ = 0 := by
  rw [Kernel.pow_add, pow_one] at hx
  exact Kernel.ae_null_of_comp_null hx

variable (U : Set X) (hU : MeasurableSet U)
  (Q : (U →ᵇ 𝕜) →L[𝕜] (U →ᵇ 𝕜))
  (hQ : ∀ (g : U →ᵇ 𝕜) (x : U), (Q g) x =
    ∫ y, g y ∂LeanShared.SubtypeKernel.restrict C.killedTransition U hU x)

include hQ

omit [OpensMeasurableSpace X] in
/-- Full-chain finite extinction also kills the same restricted transfer
power. This is proved using the actual positive subtype kernel. -/
theorem subtype_power_zero_of_full_extinction (N : ℕ) (g : U →ᵇ 𝕜) (x : U)
    (hx : (C.killedTransition ^ N) x.val univ = 0) : (Q ^ N) g x = 0 := by
  induction N generalizing x with
  | zero =>
      change (Measure.dirac x.val) univ = 0 at hx
      simp at hx
  | succ N ih =>
      have ha := ae_extinction_predecessor C N x.val hx
      have hsub : ∀ᵐ y : U ∂LeanShared.SubtypeKernel.restrict C.killedTransition U hU x,
          (C.killedTransition ^ N) y.val univ = 0 :=
        (ae_restrict_iff_subtype hU).1 (ae_restrict_of_ae ha)
      rw [pow_succ', mul_apply_eq_comp, hQ]
      have heq : (fun y : U => ((Q ^ N) g) y) =ᵐ[
          LeanShared.SubtypeKernel.restrict C.killedTransition U hU x] 0 := by
        filter_upwards [hsub] with y hy
        exact ih y hy
      rw [integral_congr_ae heq]
      simp only [Pi.zero_apply, integral_zero]

end Extinction

section Entrance

variable (C : AbsorbingMarkovChains.CanonicalChain X) (U : Set X) (hU : MeasurableSet U)
  (Q : (U →ᵇ 𝕜) →L[𝕜] (U →ᵇ 𝕜))
  (D : (↥(Uᶜ) →ᵇ 𝕜) →L[𝕜] (↥(Uᶜ) →ᵇ 𝕜))
  (S : (U →ᵇ 𝕜) →L[𝕜] (X →ᵇ 𝕜))
  (hQ : ∀ (g : U →ᵇ 𝕜) (x : U), (Q g) x =
    ∫ y, g y ∂LeanShared.SubtypeKernel.restrict C.killedTransition U hU x)
  (hD : ∀ (g : ↥(Uᶜ) →ᵇ 𝕜) (x : ↥(Uᶜ)), (D g) x =
    ∫ y, g y ∂LeanShared.SubtypeKernel.restrict C.killedTransition Uᶜ hU.compl x)
  (hS : ∀ (g : U →ᵇ 𝕜) (x : X), (S g) x =
    ∫ y : U, g y ∂(C.killedTransition x).comap Subtype.val)

include hQ hD hS

omit [OpensMeasurableSpace X] in
/-- Positive full-kernel extinction annihilates every first-entrance prefix
followed by a sufficiently long restricted-transfer power. -/
theorem first_entrance_power_zero_of_full_extinction (N j : ℕ) (g : U →ᵇ 𝕜)
    (x : ↥(Uᶜ)) (hx : (C.killedTransition ^ N) x.val univ = 0) :
    ((D ^ j) (restrictObservable Uᶜ (S ((Q ^ N) g)))) x = 0 := by
  induction j generalizing x with
  | zero =>
      simp only [pow_zero, one_apply_eq_self, restrictObservable_apply, hS]
      have ha := ae_extinction_successor C N x.val hx
      have hsub : ∀ᵐ y : U ∂(C.killedTransition x.val).comap Subtype.val,
          (C.killedTransition ^ N) y.val univ = 0 :=
        (ae_restrict_iff_subtype hU).1 (ae_restrict_of_ae ha)
      have heq : (fun y : U => ((Q ^ N) g) y) =ᵐ[
          (C.killedTransition x.val).comap Subtype.val] 0 := by
        filter_upwards [hsub] with y hy
        exact subtype_power_zero_of_full_extinction C U hU Q hQ N g y hy
      rw [integral_congr_ae heq]
      simp only [Pi.zero_apply, integral_zero]
  | succ j ih =>
      rw [pow_succ', mul_apply_eq_comp, hD]
      have ha := ae_extinction_successor C N x.val hx
      have hsub : ∀ᵐ y : ↥(Uᶜ) ∂LeanShared.SubtypeKernel.restrict
          C.killedTransition Uᶜ hU.compl x,
          (C.killedTransition ^ N) y.val univ = 0 :=
        (ae_restrict_iff_subtype hU.compl).1 (ae_restrict_of_ae ha)
      have heq : (fun y : ↥(Uᶜ) =>
          ((D ^ j) (restrictObservable Uᶜ (S ((Q ^ N) g)))) y) =ᵐ[
          LeanShared.SubtypeKernel.restrict C.killedTransition Uᶜ hU.compl x] 0 := by
        filter_upwards [hsub] with y hy
        exact ih y hy
      rw [integral_congr_ae heq]
      simp only [Pi.zero_apply, integral_zero]

omit [OpensMeasurableSpace X] in
/-- Each first-entrance functional vanishes on nonzero generalized spectral
vectors at full-chain extinct states. No invariant bad set is assumed. -/
theorem first_entrance_generalized_zero {z : 𝕜} (hz : z ≠ 0) (k : ℕ)
    (g : U →ᵇ 𝕜) (hg : ((Q - z • 1) ^ k) g = 0) (j : ℕ)
    (x : ↥(Uᶜ)) (N : ℕ) (hx : (C.killedTransition ^ N) x.val univ = 0) :
    ((D ^ j) (restrictObservable Uᶜ (S g))) x = 0 := by
  let ev : (U →ᵇ 𝕜) →L[𝕜] 𝕜 :=
    ((BoundedContinuousFunction.evalCLM 𝕜 x).comp (D ^ j)).comp
      ((restrictObservable Uᶜ).comp S)
  have hann : ev.comp (Q ^ N) = 0 := by
    ext f
    exact first_entrance_power_zero_of_full_extinction C U hU Q D S hQ hD hS N j f x hx
  exact LeanShared.SpectralVanishing.eval_generalized_eq_zero Q ev hz N k hann g hg

end Entrance

section SupportedPairs

variable (U B : Set X) (D : (↥(Uᶜ) →ᵇ 𝕜) →L[𝕜] (↥(Uᶜ) →ᵇ 𝕜))

/-- Complement functions whose every killed-complement iterate vanishes
on the full-chain extinct bad region. This is a function subspace, not a
continuous spatial projection. -/
def entranceGood : Submodule 𝕜 (↥(Uᶜ) →ᵇ 𝕜) where
  carrier := {v | ∀ j : ℕ, ∀ x : ↥(Uᶜ), x.val ∈ B → ((D ^ j) v) x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw j x hx
    simp only [map_add, BoundedContinuousFunction.add_apply, hv j x hx, hw j x hx, add_zero]
  smul_mem' := by
    intro a v hv j x hx
    simp only [map_smul, BoundedContinuousFunction.smul_apply, hv j x hx, smul_zero]

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem entranceGood_apply_zero (v : ↥(Uᶜ) →ᵇ 𝕜) (hv : v ∈ entranceGood U B D)
    (x : ↥(Uᶜ)) (hx : x.val ∈ B) : v x = 0 := by
  exact hv 0 x hx

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem entranceGood_map (v : ↥(Uᶜ) →ᵇ 𝕜) (hv : v ∈ entranceGood U B D) :
    D v ∈ entranceGood U B D := by
  intro j x hx
  rw [← mul_apply_eq_comp, ← pow_succ]
  exact hv (j + 1) x hx

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem entranceGood_shift (z : 𝕜) (v : ↥(Uᶜ) →ᵇ 𝕜) (hv : v ∈ entranceGood U B D) :
    (D - z • 1) v ∈ entranceGood U B D := by
  simp only [sub_apply, smul_apply, one_apply_eq_self]
  exact (entranceGood U B D).sub_mem (entranceGood_map U B D v hv)
    ((entranceGood U B D).smul_mem z hv)

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem entranceGood_shift_pow (z : 𝕜) (j : ℕ) (v : ↥(Uᶜ) →ᵇ 𝕜)
    (hv : v ∈ entranceGood U B D) :
    ((D - z • 1) ^ j) v ∈ entranceGood U B D := by
  induction j with
  | zero => simpa only [pow_zero, one_apply_eq_self] using hv
  | succ j ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact entranceGood_shift U B D z _ ih

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem entranceGood_shiftedInverse (z : 𝕜) (N : ℕ)
    (v : ↥(Uᶜ) →ᵇ 𝕜) (hv : v ∈ entranceGood U B D) :
    LeanShared.TransientRestriction.shiftedInverse D z N v ∈ entranceGood U B D := by
  have hp (j : ℕ) : ((z⁻¹ • D) ^ j) v ∈ entranceGood U B D := by
    induction j with
    | zero => simpa only [pow_zero, one_apply_eq_self] using hv
    | succ j ih =>
        rw [pow_succ', mul_apply_eq_comp, smul_apply]
        exact (entranceGood U B D).smul_mem z⁻¹ (entranceGood_map U B D _ ih)
  simp only [LeanShared.TransientRestriction.shiftedInverse,
    LeanShared.TransientRestriction.finiteResolvent, neg_apply, smul_apply,
    sum_apply]
  apply (entranceGood U B D).neg_mem
  apply (entranceGood U B D).smul_mem
  exact (entranceGood U B D).sum_mem (fun j _ => hp j)

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem entranceGood_shiftedInverse_pow (z : 𝕜) (N k : ℕ)
    (v : ↥(Uᶜ) →ᵇ 𝕜) (hv : v ∈ entranceGood U B D) :
    (LeanShared.TransientRestriction.shiftedInverse D z N ^ k) v ∈ entranceGood U B D := by
  induction k with
  | zero => simpa only [pow_zero, one_apply_eq_self] using hv
  | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact entranceGood_shiftedInverse U B D z N _ ih

end SupportedPairs

section Smoothing

variable (C : AbsorbingMarkovChains.CanonicalChain X) (U B : Set X) (hU : MeasurableSet U)
  (P : (X →ᵇ 𝕜) →L[𝕜] (X →ᵇ 𝕜))
  (Q : (U →ᵇ 𝕜) →L[𝕜] (U →ᵇ 𝕜))
  (D : (↥(Uᶜ) →ᵇ 𝕜) →L[𝕜] (↥(Uᶜ) →ᵇ 𝕜))
  (S : (U →ᵇ 𝕜) →L[𝕜] (X →ᵇ 𝕜))
  (Sc : (↥(Uᶜ) →ᵇ 𝕜) →L[𝕜] (X →ᵇ 𝕜))
  (hP : ∀ (f : X →ᵇ 𝕜) (x : X), (P f) x = ∫ y, f y ∂C.killedTransition x)
  (hQ : ∀ (g : U →ᵇ 𝕜) (x : U), (Q g) x =
    ∫ y, g y ∂LeanShared.SubtypeKernel.restrict C.killedTransition U hU x)
  (hD : ∀ (g : ↥(Uᶜ) →ᵇ 𝕜) (x : ↥(Uᶜ)), (D g) x =
    ∫ y, g y ∂LeanShared.SubtypeKernel.restrict C.killedTransition Uᶜ hU.compl x)
  (hS : ∀ (g : U →ᵇ 𝕜) (x : X), (S g) x =
    ∫ y : U, g y ∂(C.killedTransition x).comap Subtype.val)
  (hSc : ∀ (g : ↥(Uᶜ) →ᵇ 𝕜) (x : X), (Sc g) x =
    ∫ y : ↥(Uᶜ), g y ∂(C.killedTransition x).comap Subtype.val)

/-- The actual kernel smooths a measurable piecewise function into a
globally bounded continuous function. Both terms have already been smoothed. -/
def smoothPair : ((U →ᵇ 𝕜) × (↥(Uᶜ) →ᵇ 𝕜)) →L[𝕜] (X →ᵇ 𝕜) :=
  S.comp (ContinuousLinearMap.fst 𝕜 _ _) + Sc.comp (ContinuousLinearMap.snd 𝕜 _ _)

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem smoothPair_apply (u : U →ᵇ 𝕜) (v : ↥(Uᶜ) →ᵇ 𝕜) :
    smoothPair U S Sc (u, v) = S u + Sc v := rfl

include hP hS hSc hU in
/-- Smoothing the two restrictions reconstructs the actual full transfer. -/
theorem smoothPair_reconstruct (f : X →ᵇ 𝕜) :
    smoothPair U S Sc (restrictObservable U f, restrictObservable Uᶜ f) = P f := by
  ext x
  simp only [smoothPair_apply, BoundedContinuousFunction.add_apply, hS, hSc,
    restrictObservable_apply, integral_subtype_comap hU, integral_subtype_comap hU.compl, hP]
  have : IsFiniteMeasure (C.killedTransition x) := by
    change IsFiniteMeasure (C.toKilledKernel.kernel x)
    infer_instance
  exact integral_add_compl hU
    (Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
      (ae_of_all _ f.norm_coe_le_norm))

omit [OpensMeasurableSpace X] in
include hQ hS in
theorem restrict_smoothing (u : U →ᵇ 𝕜) : restrictObservable U (S u) = Q u := by
  ext x
  rw [restrictObservable_apply, hS, hQ]
  rfl

omit [OpensMeasurableSpace X] in
include hD hSc in
theorem complement_smoothPair (u : U →ᵇ 𝕜) (v : ↥(Uᶜ) →ᵇ 𝕜) :
    restrictObservable Uᶜ (smoothPair U S Sc (u, v)) =
      (restrictObservable Uᶜ).comp S u + D v := by
  ext x
  simp only [smoothPair_apply, map_add, BoundedContinuousFunction.add_apply,
    restrictObservable_apply, ContinuousLinearMap.comp_apply, hSc, hD]
  rfl

variable (hreturn : ∀ x : U, ∀ᵐ y ∂C.killedTransition x.val, y ∉ U → y ∈ B)

omit [OpensMeasurableSpace X] in
include hSc hreturn hU in
/-- Exits from the retained region land where the complement function is
zero. Its smoothing therefore contributes zero at retained starting states. -/
theorem restrict_complement_smoothing_zero (v : ↥(Uᶜ) →ᵇ 𝕜)
    (hv : v ∈ entranceGood U B D) : restrictObservable U (Sc v) = 0 := by
  ext x
  rw [restrictObservable_apply, hSc]
  have ha : ∀ᵐ y ∂C.killedTransition x.val, y ∈ Uᶜ → y ∈ B := hreturn x
  have hs : ∀ᵐ y : ↥(Uᶜ) ∂(C.killedTransition x.val).comap Subtype.val, y.val ∈ B := by
    have hr := (ae_restrict_iff_subtype hU.compl).1
      ((ae_restrict_iff' hU.compl).2 ha)
    exact hr
  have heq : (fun y : ↥(Uᶜ) => v y) =ᵐ[(C.killedTransition x.val).comap Subtype.val] 0 := by
    filter_upwards [hs] with y hy
    exact entranceGood_apply_zero U B D v hv y hy
  rw [integral_congr_ae heq]
  simp

include hP hQ hD hS hSc hreturn in
/-- The full transfer intertwines the finite lower-triangular algebra only
on pairs whose complement coordinate has the proved spectral support control. -/
theorem smoothPair_transfer (u : U →ᵇ 𝕜) (v : ↥(Uᶜ) →ᵇ 𝕜)
    (hv : v ∈ entranceGood U B D) :
    P (smoothPair U S Sc (u, v)) = smoothPair U S Sc
      (LeanShared.TransientRestriction.block Q ((restrictObservable Uᶜ).comp S) D (u, v)) := by
  rw [← smoothPair_reconstruct C U hU P S Sc hP hS hSc]
  have hfirst : restrictObservable U (smoothPair U S Sc (u, v)) = Q u := by
    rw [smoothPair_apply, map_add, restrict_smoothing C U hU Q S hQ hS,
      restrict_complement_smoothing_zero C U B hU D Sc hSc hreturn v hv, add_zero]
  rw [hfirst, complement_smoothPair C U hU D S Sc hD hSc,
    LeanShared.TransientRestriction.block_apply]

variable (hext : ∀ x ∈ B, ∃ N : ℕ,
    C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival N) = 0)

omit [OpensMeasurableSpace X] in
include hQ hD hS hext in
/-- Actual full-chain extinction supplies the precise support property of
the entrance coupling on every nonzero generalized eigenspace. -/
theorem entrance_coupling_good {z : 𝕜} (hz : z ≠ 0) (k : ℕ)
    (u : U →ᵇ 𝕜) (hu : ((Q - z • 1) ^ k) u = 0) :
    (restrictObservable Uᶜ).comp S u ∈ entranceGood U B D := by
  intro j x hx
  obtain ⟨N, hN⟩ := hext x.val hx
  rw [C.pathMeasure_survival] at hN
  exact first_entrance_generalized_zero C U hU Q D S hQ hD hS hz k u hu j x N hN

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem generalized_shift_pow (Q : (U →ᵇ 𝕜) →L[𝕜] (U →ᵇ 𝕜)) (z : 𝕜)
    (k j : ℕ) (u : U →ᵇ 𝕜) (hu : ((Q - z • 1) ^ k) u = 0) :
    ((Q - z • 1) ^ k) (((Q - z • 1) ^ j) u) = 0 := by
  rw [← mul_apply_eq_comp, ← pow_add, Nat.add_comm, pow_add,
    mul_apply_eq_comp, hu, map_zero]

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- A finite polynomial in the shifted transfer solves `Q u = g` on the
generalized eigenspace of any nonzero scalar. Global invertibility is not assumed. -/
theorem exists_generalized_preimage (Q : (U →ᵇ 𝕜) →L[𝕜] (U →ᵇ 𝕜))
    {z : 𝕜} (hz : z ≠ 0) (k : ℕ) (g : U →ᵇ 𝕜)
    (hg : ((Q - z • 1) ^ k) g = 0) :
    ∃ u : U →ᵇ 𝕜, Q u = g ∧ ((Q - z • 1) ^ k) u = 0 := by
  induction k generalizing g with
  | zero =>
      have hg0 : g = 0 := by simpa only [pow_zero, one_apply_eq_self] using hg
      refine ⟨0, ?_, ?_⟩
      · rw [map_zero, hg0]
      · simp
  | succ k ih =>
      have hshift : ((Q - z • 1) ^ k) ((Q - z • 1) g) = 0 := by
        rw [← mul_apply_eq_comp, ← pow_succ]
        exact hg
      obtain ⟨v, hQv, hv⟩ := ih ((Q - z • 1) g) hshift
      have hvnext : ((Q - z • 1) ^ (k + 1)) v = 0 := by
        rw [pow_succ', mul_apply_eq_comp, hv, map_zero]
      refine ⟨z⁻¹ • (g - v), ?_, ?_⟩
      · rw [map_smul, map_sub, hQv]
        simp only [sub_apply, smul_apply, one_apply_eq_self, sub_sub_cancel,
          smul_smul, inv_mul_cancel₀ hz, one_smul]
      · rw [map_smul, map_sub, hg, hvnext, sub_self, smul_zero]

omit [OpensMeasurableSpace X] in
include hQ hD hS hext in
theorem shifted_powerCoupling_good {z : 𝕜} (hz : z ≠ 0) (k : ℕ)
    (u : U →ᵇ 𝕜) (hu : ((Q - z • 1) ^ k) u = 0) (j : ℕ) :
    LeanShared.TransientRestriction.powerCoupling (Q - z • 1)
      ((restrictObservable Uᶜ).comp S) (D - z • 1) j u ∈ entranceGood U B D := by
  induction j with
  | zero => exact (entranceGood U B D).zero_mem
  | succ j ih =>
      simp only [LeanShared.TransientRestriction.powerCoupling, add_apply,
        ContinuousLinearMap.comp_apply]
      exact (entranceGood U B D).add_mem
        (entrance_coupling_good C U B hU Q D S hQ hD hS hext hz k _
          (generalized_shift_pow U Q z k j u hu))
        (entranceGood_shift U B D z _ ih)

include hP hQ hD hS hSc hreturn hext in
/-- Smoothing preserves generalized eigenvector equations for the finite
entrance lift, whose complement coordinate has the derived support control. -/
theorem smoothPair_generalized {z : 𝕜} (hz : z ≠ 0) (k : ℕ)
    (u : U →ᵇ 𝕜) (v : ↥(Uᶜ) →ᵇ 𝕜)
    (hu : ((Q - z • 1) ^ k) u = 0) (hv : v ∈ entranceGood U B D)
    (hw : ((LeanShared.TransientRestriction.block Q
      ((restrictObservable Uᶜ).comp S) D - z • 1) ^ k) (u, v) = 0) :
    ((P - z • 1) ^ k) (smoothPair U S Sc (u, v)) = 0 := by
  let T := LeanShared.TransientRestriction.block Q ((restrictObservable Uᶜ).comp S) D
  have hgood (j : ℕ) : (((T - z • 1) ^ j) (u, v)).2 ∈ entranceGood U B D := by
    simp only [T, LeanShared.TransientRestriction.block_sub_scalar,
      LeanShared.TransientRestriction.block_pow, LeanShared.TransientRestriction.block_apply]
    exact (entranceGood U B D).add_mem
      (shifted_powerCoupling_good C U B hU Q D S hQ hD hS hext hz k u hu j)
      (entranceGood_shift_pow U B D z j v hv)
  have hshift (w : (U →ᵇ 𝕜) × (↥(Uᶜ) →ᵇ 𝕜))
      (hvg : w.2 ∈ entranceGood U B D) :
      (P - z • 1) (smoothPair U S Sc w) = smoothPair U S Sc ((T - z • 1) w) := by
    simp only [sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul]
    rw [smoothPair_transfer C U B hU P Q D S Sc hP hQ hD hS hSc hreturn w.1 w.2 hvg]
  have hp (j : ℕ) : ((P - z • 1) ^ j) (smoothPair U S Sc (u, v)) =
      smoothPair U S Sc (((T - z • 1) ^ j) (u, v)) := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', mul_apply_eq_comp, ih, hshift _ (hgood j),
        pow_succ', mul_apply_eq_comp]
  rw [hp k, hw, map_zero]

include hP hQ hD hS hSc hreturn hext in
/-- Finite entrance algebra, actual support control and one kernel
smoothing produce a genuine global continuous generalized eigenfunction
with the prescribed restriction. -/
theorem exists_generalized_lift (N : ℕ) (hDnil : D ^ N = 0)
    {z : 𝕜} (hz : z ≠ 0) (k : ℕ) (g : U →ᵇ 𝕜)
    (hg : ((Q - z • 1) ^ k) g = 0) :
    ∃ f : X →ᵇ 𝕜, restrictObservable U f = g ∧ ((P - z • 1) ^ k) f = 0 := by
  obtain ⟨u, hQu, hu⟩ := exists_generalized_preimage U Q hz k g hg
  let E := LeanShared.TransientRestriction.generalizedRestrictionEquiv Q
    ((restrictObservable Uᶜ).comp S) D hz N hDnil k
  let w := E.symm ⟨u, hu⟩
  let v := w.1.2
  have hwfirst : w.1.1 = u := by
    have h := LeanShared.TransientRestriction.generalizedRestrictionEquiv_apply Q
      ((restrictObservable Uᶜ).comp S) D hz N hDnil k w
    rw [show E w = ⟨u, hu⟩ from E.apply_symm_apply ⟨u, hu⟩] at h
    exact h.symm
  have hw : ((LeanShared.TransientRestriction.block Q
      ((restrictObservable Uᶜ).comp S) D - z • 1) ^ k) (u, v) = 0 := by
    have h := w.2
    change ((LeanShared.TransientRestriction.block Q
      ((restrictObservable Uᶜ).comp S) D - z • 1) ^ k) w.1 = 0 at h
    have heq : w.1 = (u, v) := Prod.ext hwfirst rfl
    rw [heq] at h
    exact h
  have hv : v ∈ entranceGood U B D := by
    have h := LeanShared.TransientRestriction.generalizedRestrictionEquiv_symm_apply Q
      ((restrictObservable Uᶜ).comp S) D hz N hDnil k ⟨u, hu⟩
    have hvformula := congrArg Prod.snd h
    change v = _ at hvformula
    rw [hvformula]
    exact (entranceGood U B D).neg_mem
      (entranceGood_shiftedInverse_pow U B D z N k _
        (shifted_powerCoupling_good C U B hU Q D S hQ hD hS hext hz k u hu k))
  refine ⟨smoothPair U S Sc (u, v), ?_, ?_⟩
  · rw [smoothPair_apply, map_add, restrict_smoothing C U hU Q S hQ hS,
      restrict_complement_smoothing_zero C U B hU D Sc hSc hreturn v hv, add_zero, hQu]
  · exact smoothPair_generalized C U B hU P Q D S Sc hP hQ hD hS hSc hreturn hext
      hz k u v hu hv hw

include hP hQ hD hS hSc hreturn hext in
/-- Every nonzero subtype eigenfunction has a nonzero global continuous
eigenfunction lift for the actual kernel. -/
theorem exists_eigenfunction_lift (N : ℕ) (hDnil : D ^ N = 0)
    {z : 𝕜} (hz : z ≠ 0) (g : U →ᵇ 𝕜) (hg : Q g = z • g) (hne : g ≠ 0) :
    ∃ f : X →ᵇ 𝕜, restrictObservable U f = g ∧ P f = z • f ∧ f ≠ 0 := by
  have hgen : ((Q - z • 1) ^ (1 : ℕ)) g = 0 := by
    simp only [pow_one, sub_apply, smul_apply, one_apply_eq_self, hg, sub_self]
  obtain ⟨f, hRf, hf⟩ := exists_generalized_lift C U B hU P Q D S Sc hP hQ hD hS hSc
    hreturn hext N hDnil hz 1 g hgen
  refine ⟨f, hRf, ?_, ?_⟩
  · simpa only [pow_one, sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] using hf
  · intro hzero
    exact hne (by rw [← hRf, hzero, map_zero])

end Smoothing

section StrongFeller

variable (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (U : Set X) (hU : MeasurableSet U)

/-- The actual subtype transfer constructed by full-kernel smoothing and
continuous restriction. Its inputs are only the usual real strong-Feller property. -/
def smoothedSubtypeTransfer : (U →ᵇ 𝕜) →L[𝕜] (U →ᵇ 𝕜) :=
  (restrictObservable U).comp (ComplexStrongFeller.extensionOperator C hSF U hU)

theorem smoothedSubtypeTransfer_represents (g : U →ᵇ 𝕜) (x : U) :
    smoothedSubtypeTransfer (𝕜 := 𝕜) C hSF U hU g x =
      ∫ y, g y ∂LeanShared.SubtypeKernel.restrict C.killedTransition U hU x := by
  exact ComplexStrongFeller.extensionOperator_apply_subtype C hSF U hU g x.val

/-- Every power of the constructed subtype transfer is the actual subtype
kernel-power integral. -/
theorem smoothedSubtypeTransfer_power_represents (n : ℕ) (g : U →ᵇ 𝕜) (x : U) :
    ((smoothedSubtypeTransfer C hSF U hU) ^ n) g x =
      ∫ y, g y ∂((LeanShared.SubtypeKernel.restrict C.killedTransition U hU) ^ n) x := by
  let : IsFiniteKernel C.killedTransition := by
    change IsFiniteKernel C.toKilledKernel.kernel
    infer_instance
  let K := LeanShared.SubtypeKernel.restrict C.killedTransition U hU
  let : IsFiniteKernel K := by
    dsimp [K, LeanShared.SubtypeKernel.restrict]
    infer_instance
  have hfinite (m : ℕ) : IsFiniteKernel (K ^ m) := by
    induction m with
    | zero => change IsFiniteKernel Kernel.id; infer_instance
    | succ m ih =>
        rw [Kernel.pow_add, pow_one]
        let : IsFiniteKernel (K ^ m) := ih
        infer_instance
  induction n generalizing x with
  | zero =>
      change g x = ∫ y, g y ∂Measure.dirac x
      exact (integral_dirac' g x g.continuous.measurable.stronglyMeasurable).symm
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, smoothedSubtypeTransfer_represents]
      simp_rw [ih]
      rw [Kernel.pow_add, pow_one]
      let : IsFiniteKernel (K ^ n) := hfinite n
      have hint : Integrable (fun y : U => g y) (((K ^ n) ∘ₖ K) x) :=
        Integrable.of_bound g.continuous.measurable.aestronglyMeasurable ‖g‖
          (ae_of_all _ g.norm_coe_le_norm)
      exact (Kernel.integral_comp hint).symm

/-- Finite extinction of the actual subtype kernel discharges the
nilpotent-complement input of the lifting construction. -/
theorem smoothedSubtypeTransfer_nilpotent_of_kernel_extinction (N : ℕ)
    (hext : ∀ x : U,
      ((LeanShared.SubtypeKernel.restrict C.killedTransition U hU) ^ N) x univ = 0) :
    (smoothedSubtypeTransfer (𝕜 := 𝕜) C hSF U hU) ^ N = 0 := by
  ext g x
  rw [smoothedSubtypeTransfer_power_represents]
  have hz : ((LeanShared.SubtypeKernel.restrict C.killedTransition U hU) ^ N) x = 0 :=
    Measure.measure_univ_eq_zero.mp (hext x)
  rw [hz, integral_zero_measure]
  rfl

include hSF in
/-- Standard strong-Feller continuity supplies every smoothing and transfer
operator in the finite lifting theorem, over real or complex scalars. -/
theorem exists_strongFeller_generalized_lift (B : Set X)
    (hreturn : ∀ x : U, ∀ᵐ y ∂C.killedTransition x.val, y ∉ U → y ∈ B)
    (hext : ∀ x ∈ B, ∃ n : ℕ,
      C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (N : ℕ) (hnil : (smoothedSubtypeTransfer (𝕜 := 𝕜) C hSF Uᶜ hU.compl) ^ N = 0)
    {z : 𝕜} (hz : z ≠ 0) (k : ℕ) (g : U →ᵇ 𝕜)
    (hg : ((smoothedSubtypeTransfer (𝕜 := 𝕜) C hSF U hU - z • 1) ^ k) g = 0) :
    ∃ f : X →ᵇ 𝕜, restrictObservable U f = g ∧
      ((ComplexStrongFeller.transferOperator (𝕜 := 𝕜) C hSF - z • 1) ^ k) f = 0 :=
  exists_generalized_lift C U B hU
    (ComplexStrongFeller.transferOperator (𝕜 := 𝕜) C hSF)
    (smoothedSubtypeTransfer C hSF U hU)
    (smoothedSubtypeTransfer C hSF Uᶜ hU.compl)
    (ComplexStrongFeller.extensionOperator C hSF U hU)
    (ComplexStrongFeller.extensionOperator C hSF Uᶜ hU.compl)
    (ComplexStrongFeller.transferOperator_apply C hSF)
    (smoothedSubtypeTransfer_represents C hSF U hU)
    (smoothedSubtypeTransfer_represents C hSF Uᶜ hU.compl)
    (ComplexStrongFeller.extensionOperator_apply_subtype C hSF U hU)
    (ComplexStrongFeller.extensionOperator_apply_subtype C hSF Uᶜ hU.compl)
    hreturn hext N hnil hz k g hg

include hSF in
/-- Kernel-level finite complement extinction and standard strong Feller
regularity suffice for actual continuous generalized spectral lifting.
Every operator and smoothing map is constructed from the killed kernel. -/
theorem exists_strongFeller_lift_of_complement_extinction (B : Set X)
    (hreturn : ∀ x : U, ∀ᵐ y ∂C.killedTransition x.val, y ∉ U → y ∈ B)
    (hext : ∀ x ∈ B, ∃ n : ℕ,
      C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (N : ℕ) (hcomp : ∀ x : ↥(Uᶜ),
      ((LeanShared.SubtypeKernel.restrict C.killedTransition Uᶜ hU.compl) ^ N) x univ = 0)
    {z : 𝕜} (hz : z ≠ 0) (k : ℕ) (g : U →ᵇ 𝕜)
    (hg : ((smoothedSubtypeTransfer (𝕜 := 𝕜) C hSF U hU - z • 1) ^ k) g = 0) :
    ∃ f : X →ᵇ 𝕜, restrictObservable U f = g ∧
      ((ComplexStrongFeller.transferOperator (𝕜 := 𝕜) C hSF - z • 1) ^ k) f = 0 :=
  exists_strongFeller_generalized_lift C hSF U hU B hreturn hext N
    (smoothedSubtypeTransfer_nilpotent_of_kernel_extinction C hSF Uᶜ hU.compl N hcomp)
    hz k g hg

end StrongFeller

end ConditionedStochasticStabilityHyperbolic.Restriction
