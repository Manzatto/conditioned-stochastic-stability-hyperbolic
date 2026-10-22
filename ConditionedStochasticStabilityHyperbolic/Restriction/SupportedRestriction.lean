module

public import ConditionedStochasticStabilityHyperbolic.Restriction.EigenfunctionSupport
public import LeanShared.Probability.SubtypeKernel

/-!
# Restriction on supported generalized eigenfunctions

Restriction intertwines the actual full and subtype killed transfers on the
nonzero generalized eigenspaces. The geometric hypothesis only controls live
transitions leaving the smaller region: they land in a finitely extinct bad
region. No spatial zero extension or continuous block decomposition is used.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Restriction

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {𝕜 : Type*} [RCLike 𝕜]

/-- Restriction is continuous precomposition with the subtype inclusion. -/
def restrictObservable (U : Set X) : (X →ᵇ 𝕜) →L[𝕜] (U →ᵇ 𝕜) :=
  BoundedContinuousFunction.compContinuousCLM 𝕜 𝕜 ⟨Subtype.val, continuous_subtype_val⟩

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
@[simp]
theorem restrictObservable_apply (U : Set X) (f : X →ᵇ 𝕜) (x : U) :
    restrictObservable U f x = f x.val := rfl

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- The full and restricted integrals agree whenever the observable vanishes
at almost every destination outside the smaller region. -/
theorem integral_subtype_of_ae_outside_zero (K : Kernel X X) (U : Set X)
    (hU : MeasurableSet U) (f : X → 𝕜) (x : U)
    (hout : ∀ᵐ y ∂K x.val, y ∉ U → f y = 0) :
    (∫ y : U, f y.val ∂LeanShared.SubtypeKernel.restrict K U hU x) =
      ∫ y, f y ∂K x.val := by
  rw [← (MeasurableEmbedding.subtype_coe hU).integral_map f,
    LeanShared.SubtypeKernel.map_restrict_apply]
  exact setIntegral_eq_integral_of_ae_compl_eq_zero hout

omit [OpensMeasurableSpace X] in
/-- A function that vanishes everywhere outside the subtype has exact
one-step restriction, irrespective of transition support. -/
theorem restrict_transfer_of_vanishes_outside
    (K : Kernel X X) (U : Set X) (hU : MeasurableSet U)
    (P : (X →ᵇ 𝕜) →L[𝕜] (X →ᵇ 𝕜))
    (Q : (U →ᵇ 𝕜) →L[𝕜] (U →ᵇ 𝕜))
    (hP : ∀ (f : X →ᵇ 𝕜) (x : X), (P f) x = ∫ y, f y ∂K x)
    (hQ : ∀ (g : U →ᵇ 𝕜) (x : U), (Q g) x =
      ∫ y, g y ∂LeanShared.SubtypeKernel.restrict K U hU x)
    (f : X →ᵇ 𝕜) (hout : ∀ y ∉ U, f y = 0) :
    restrictObservable U (P f) = Q (restrictObservable U f) := by
  ext x
  rw [restrictObservable_apply, hP, hQ]
  symm
  exact integral_subtype_of_ae_outside_zero K U hU f x (ae_of_all _ hout)

section Spectral

variable (C : AbsorbingMarkovChains.CanonicalChain X) (U B : Set X)
  (hU : MeasurableSet U)
  (P : (X →ᵇ 𝕜) →L[𝕜] (X →ᵇ 𝕜))
  (Q : (U →ᵇ 𝕜) →L[𝕜] (U →ᵇ 𝕜))
  (hP : ∀ (f : X →ᵇ 𝕜) (x : X), (P f) x = ∫ y, f y ∂C.killedTransition x)
  (hQ : ∀ (g : U →ᵇ 𝕜) (x : U), (Q g) x =
    ∫ y, g y ∂LeanShared.SubtypeKernel.restrict C.killedTransition U hU x)
  (hext : ∀ x ∈ B, ∃ N : ℕ,
    C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival N) = 0)
  (hreturn : ∀ x : U, ∀ᵐ y ∂C.killedTransition x.val, y ∉ U → y ∈ B)

include hP hQ hext hreturn

/-- One-step intertwining holds on the actual nonzero generalized
eigenspaces, without asserting a full operator intertwining identity. -/
theorem restrict_transfer_generalized {z : 𝕜} (hz : z ≠ 0) (k : ℕ)
    (f : X →ᵇ 𝕜) (hgen : ((P - z • 1) ^ k) f = 0) :
    restrictObservable U (P f) = Q (restrictObservable U f) := by
  ext x
  rw [restrictObservable_apply, hP, hQ]
  symm
  apply integral_subtype_of_ae_outside_zero
  have hv := generalized_eigenfunction_vanishes_on_region C P hP hz k f hgen B hext
  filter_upwards [hreturn x] with y hy hout
  exact hv y (hy hout)

/-- The shifted transfer also intertwines on each generalized eigenspace. -/
theorem restrict_shift_generalized {z : 𝕜} (hz : z ≠ 0) (k : ℕ)
    (f : X →ᵇ 𝕜) (hgen : ((P - z • 1) ^ k) f = 0) :
    restrictObservable U ((P - z • 1) f) =
      (Q - z • 1) (restrictObservable U f) := by
  simp only [sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul]
  rw [restrict_transfer_generalized C U B hU P Q hP hQ hext hreturn hz k f hgen]

/-- All shifted powers intertwine on each generalized eigenspace. -/
theorem restrict_shift_pow_generalized {z : 𝕜} (hz : z ≠ 0) (k : ℕ)
    (f : X →ᵇ 𝕜) (hgen : ((P - z • 1) ^ k) f = 0) (j : ℕ) :
    restrictObservable U (((P - z • 1) ^ j) f) =
      ((Q - z • 1) ^ j) (restrictObservable U f) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hg : ((P - z • 1) ^ k) (((P - z • 1) ^ j) f) = 0 := by
        rw [← mul_apply_eq_comp, ← pow_add, Nat.add_comm, pow_add,
          mul_apply_eq_comp, hgen, map_zero]
      rw [pow_succ', mul_apply_eq_comp,
        restrict_shift_generalized C U B hU P Q hP hQ hext hreturn hz k _ hg,
        ih, pow_succ', mul_apply_eq_comp]

/-- Restriction preserves every finite generalized eigenvector equation. -/
theorem restrict_generalized_eigenfunction {z : 𝕜} (hz : z ≠ 0) (k : ℕ)
    (f : X →ᵇ 𝕜) (hgen : ((P - z • 1) ^ k) f = 0) :
    ((Q - z • 1) ^ k) (restrictObservable U f) = 0 := by
  rw [← restrict_shift_pow_generalized C U B hU P Q hP hQ hext hreturn hz k f hgen k,
    hgen, map_zero]

/-- In particular, restriction preserves the eigenvector equation. -/
theorem restrict_eigenfunction {z : 𝕜} (hz : z ≠ 0)
    (f : X →ᵇ 𝕜) (heig : P f = z • f) :
    Q (restrictObservable U f) = z • restrictObservable U f := by
  have hg : ((P - z • 1) ^ (1 : ℕ)) f = 0 := by
    simp only [pow_one, sub_apply, smul_apply, one_apply_eq_self, heig, sub_self]
  rw [← restrict_transfer_generalized C U B hU P Q hP hQ hext hreturn hz 1 f hg,
    heig, map_smul]

/-- Restriction is injective on each nonzero generalized eigenspace when
the actual killed-complement transfer is represented and nilpotent. The
proof restricts only the shifted spectral orbit; it never extends subtype
functions by a discontinuous indicator. -/
theorem generalized_eigenfunction_eq_zero_of_restrict_zero
    (D : (↥(Uᶜ) →ᵇ 𝕜) →L[𝕜] (↥(Uᶜ) →ᵇ 𝕜))
    (hD : ∀ (g : ↥(Uᶜ) →ᵇ 𝕜) (x : ↥(Uᶜ)), (D g) x =
      ∫ y, g y ∂LeanShared.SubtypeKernel.restrict C.killedTransition Uᶜ hU.compl x)
    (N : ℕ) (hDnil : D ^ N = 0) {z : 𝕜} (hz : z ≠ 0) (k : ℕ)
    (f : X →ᵇ 𝕜) (hgen : ((P - z • 1) ^ k) f = 0)
    (hRf : restrictObservable U f = 0) : f = 0 := by
  have hRU (j : ℕ) : restrictObservable U (((P - z • 1) ^ j) f) = 0 := by
    rw [restrict_shift_pow_generalized C U B hU P Q hP hQ hext hreturn hz k f hgen j,
      hRf, map_zero]
  have hRC (j : ℕ) : restrictObservable Uᶜ (((P - z • 1) ^ j) f) =
      ((D - z • 1) ^ j) (restrictObservable Uᶜ f) := by
    induction j with
    | zero => simp
    | succ j ih =>
        have hout : ∀ y ∉ Uᶜ, (((P - z • 1) ^ j) f) y = 0 := by
          intro y hy
          have hyU : y ∈ U := by simpa only [mem_compl_iff, not_not] using hy
          exact congrArg (fun g : U →ᵇ 𝕜 => g ⟨y, hyU⟩) (hRU j)
        rw [pow_succ', mul_apply_eq_comp]
        simp only [sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul]
        rw [restrict_transfer_of_vanishes_outside C.killedTransition Uᶜ hU.compl
          P D hP hD _ hout, ih]
        rw [pow_succ', mul_apply_eq_comp]
        simp only [sub_apply, smul_apply, one_apply_eq_self]
  have hRcgen : ((D - z • 1) ^ k) (restrictObservable Uᶜ f) = 0 := by
    rw [← hRC k, hgen, map_zero]
  ext x
  by_cases hx : x ∈ U
  · exact congrArg (fun g : U →ᵇ 𝕜 => g ⟨x, hx⟩) hRf
  · exact LeanShared.SpectralVanishing.eval_generalized_eq_zero D
      (BoundedContinuousFunction.evalCLM 𝕜 (⟨x, hx⟩ : ↥(Uᶜ))) hz N k
      (by rw [hDnil]; simp) (restrictObservable Uᶜ f) hRcgen

/-- A nonzero generalized eigenfunction has nonzero restriction under the
same represented finite-transience condition on the complement. -/
theorem restrict_generalized_eigenfunction_ne_zero
    (D : (↥(Uᶜ) →ᵇ 𝕜) →L[𝕜] (↥(Uᶜ) →ᵇ 𝕜))
    (hD : ∀ (g : ↥(Uᶜ) →ᵇ 𝕜) (x : ↥(Uᶜ)), (D g) x =
      ∫ y, g y ∂LeanShared.SubtypeKernel.restrict C.killedTransition Uᶜ hU.compl x)
    (N : ℕ) (hDnil : D ^ N = 0) {z : 𝕜} (hz : z ≠ 0) (k : ℕ)
    (f : X →ᵇ 𝕜) (hgen : ((P - z • 1) ^ k) f = 0) (hf : f ≠ 0) :
    restrictObservable U f ≠ 0 := by
  intro hRf
  exact hf (generalized_eigenfunction_eq_zero_of_restrict_zero C U B hU P Q hP hQ
    hext hreturn D hD N hDnil hz k f hgen hRf)

/-- Two vectors in the same finite generalized eigenspace are equal if
their restrictions agree. This is injectivity on that eigenspace, not an
injectivity claim for all bounded continuous observables. -/
theorem generalized_eigenfunction_eq_of_restrict_eq
    (D : (↥(Uᶜ) →ᵇ 𝕜) →L[𝕜] (↥(Uᶜ) →ᵇ 𝕜))
    (hD : ∀ (g : ↥(Uᶜ) →ᵇ 𝕜) (x : ↥(Uᶜ)), (D g) x =
      ∫ y, g y ∂LeanShared.SubtypeKernel.restrict C.killedTransition Uᶜ hU.compl x)
    (N : ℕ) (hDnil : D ^ N = 0) {z : 𝕜} (hz : z ≠ 0) (k : ℕ)
    (f g : X →ᵇ 𝕜) (hf : ((P - z • 1) ^ k) f = 0)
    (hg : ((P - z • 1) ^ k) g = 0)
    (heq : restrictObservable U f = restrictObservable U g) : f = g := by
  apply sub_eq_zero.mp
  apply generalized_eigenfunction_eq_zero_of_restrict_zero C U B hU P Q hP hQ
    hext hreturn D hD N hDnil hz k (f - g)
  · rw [map_sub, hf, hg, sub_self]
  · rw [map_sub, heq, sub_self]

end Spectral

end ConditionedStochasticStabilityHyperbolic.Restriction
