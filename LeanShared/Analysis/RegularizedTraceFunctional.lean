module
public import LeanShared.Analysis.PeripheralTraceRank
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Regularized traces given by continuous families of rank-one pieces. A family
`y ↦ (ψ_y, e_y)` of tests and vectors with `∫ ‖ψ_y‖ ‖e_y‖ < ∞` defines the bounded
functional `τ(X) = ∫ ψ_y (X e_y)` on operators and the smoothing `Q v = ∫ ψ_y(v) e_y`,
with `τ(φ ⊗ v) = φ(Q v)`. If `Q_j → I` weakly on the range of a finite-rank projector,
then `τ_j` of the projector tends to its rank. Combined with the phased Cesàro lemma:
if the regularized traces of the powers of an operator with finite peripheral
decomposition stay close to periodic sums tending to `1`, the peripheral spectrum is
the single phase `1` with a rank-one projector. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Filter Finset MeasureTheory
open scoped Topology
namespace LeanShared.RegularizedTraceFunctional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y]

/-- A continuous integrable family of rank-one pieces. -/
structure Family (E Y : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace Y]
    [MeasurableSpace Y] where
  measure : Measure Y
  test : Y → E →L[ℂ] ℂ
  vector : Y → E
  continuous_test : Continuous test
  continuous_vector : Continuous vector
  integrable : Integrable (fun y => ‖test y‖ * ‖vector y‖) measure

namespace Family

variable (F : Family E Y)

theorem integrable_apply (X : E →L[ℂ] E) :
    Integrable (fun y => F.test y (X (F.vector y))) F.measure := by
  refine Integrable.mono' (F.integrable.const_mul ‖X‖)
    ((F.continuous_test.clm_apply (X.continuous.comp F.continuous_vector)).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  calc ‖F.test y (X (F.vector y))‖ ≤ ‖F.test y‖ * ‖X (F.vector y)‖ := (F.test y).le_opNorm _
    _ ≤ ‖F.test y‖ * (‖X‖ * ‖F.vector y‖) :=
        mul_le_mul_of_nonneg_left (X.le_opNorm _) (norm_nonneg _)
    _ = ‖X‖ * (‖F.test y‖ * ‖F.vector y‖) := by ring

theorem integrable_smul (v : E) :
    Integrable (fun y => F.test y v • F.vector y) F.measure := by
  refine Integrable.mono' (F.integrable.const_mul ‖v‖)
    (((F.continuous_test.clm_apply continuous_const).smul
      F.continuous_vector).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  rw [norm_smul]
  calc ‖F.test y v‖ * ‖F.vector y‖ ≤ ‖F.test y‖ * ‖v‖ * ‖F.vector y‖ :=
        mul_le_mul_of_nonneg_right ((F.test y).le_opNorm v) (norm_nonneg _)
    _ = ‖v‖ * (‖F.test y‖ * ‖F.vector y‖) := by ring

/-- The regularized trace. -/
@[expose] def traceL : (E →L[ℂ] E) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun X => ∫ y, F.test y (X (F.vector y)) ∂F.measure
      map_add' := fun X Z => by
        simp only [FunLike.coe_add, Pi.add_apply, map_add]
        exact integral_add (F.integrable_apply X) (F.integrable_apply Z)
      map_smul' := fun c X => by
        simp only [FunLike.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
    (∫ y, ‖F.test y‖ * ‖F.vector y‖ ∂F.measure) fun X => by
      change ‖∫ y, F.test y (X (F.vector y)) ∂F.measure‖ ≤ _
      calc ‖∫ y, F.test y (X (F.vector y)) ∂F.measure‖
          ≤ ∫ y, ‖X‖ * (‖F.test y‖ * ‖F.vector y‖) ∂F.measure := by
            refine norm_integral_le_of_norm_le (F.integrable.const_mul ‖X‖)
              (Eventually.of_forall fun y => ?_)
            calc ‖F.test y (X (F.vector y))‖ ≤ ‖F.test y‖ * ‖X (F.vector y)‖ :=
                  (F.test y).le_opNorm _
              _ ≤ ‖F.test y‖ * (‖X‖ * ‖F.vector y‖) :=
                  mul_le_mul_of_nonneg_left (X.le_opNorm _) (norm_nonneg _)
              _ = ‖X‖ * (‖F.test y‖ * ‖F.vector y‖) := by ring
        _ = (∫ y, ‖F.test y‖ * ‖F.vector y‖ ∂F.measure) * ‖X‖ := by
            rw [integral_const_mul, mul_comm]

theorem traceL_apply (X : E →L[ℂ] E) :
    F.traceL X = ∫ y, F.test y (X (F.vector y)) ∂F.measure := rfl

/-- The smoothing operator of the family. -/
@[expose] def smoothing (v : E) : E := ∫ y, F.test y v • F.vector y ∂F.measure

/-- Rank-one pieces: `τ(φ ⊗ v) = φ(Q v)`. -/
theorem traceL_smulRight (φ : E →L[ℂ] ℂ) (v : E) :
    F.traceL (φ.smulRight v) = φ (F.smoothing v) := by
  rw [traceL_apply, smoothing, ← ContinuousLinearMap.integral_comp_comm φ (F.integrable_smul v)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [ContinuousLinearMap.smulRight_apply, map_smul, smul_eq_mul]
  ring

end Family

/-- A finite-rank projector is a finite sum of rank-one pieces `c_i ⊗ b_i` with `c_i b_i = 1`. -/
theorem projector_expansion (P : E →L[ℂ] E) (idem : P.comp P = P)
    [FiniteDimensional ℂ (P.range)] :
    ∃ (b : Fin (Module.finrank ℂ (P.range)) → E)
      (c : Fin (Module.finrank ℂ (P.range)) → E →L[ℂ] ℂ),
      (∀ i, b i ∈ P.range) ∧ (∀ i, c i (b i) = 1) ∧
      P = ∑ i, (c i).smulRight (b i) := by
  let V := P.range
  let basis := Module.finBasis ℂ V
  let restrict : E →L[ℂ] V := P.codRestrict V (fun x => ⟨x, rfl⟩)
  let c := fun i => (LinearMap.toContinuousLinearMap (basis.coord i)).comp restrict
  have fixed (v : V) : P (v : E) = v := by
    obtain ⟨x, hx⟩ := v.property
    rw [← hx]
    exact congrArg (fun Z : E →L[ℂ] E => Z x) idem
  refine ⟨fun i => (basis i : E), c, fun i => (basis i).property, fun i => ?_, ?_⟩
  · have same : restrict (basis i : E) = basis i := Subtype.ext (fixed (basis i))
    change basis.coord i (restrict (basis i : E)) = 1
    rw [same, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  · apply ContinuousLinearMap.ext
    intro x
    have expansion := basis.sum_repr (restrict x)
    rw [show (∑ i, (c i).smulRight (basis i : E)) x = ∑ i, ((c i).smulRight (basis i : E)) x from
      map_sum (ContinuousLinearMap.apply ℂ E x) _ _]
    simp only [ContinuousLinearMap.smulRight_apply]
    have coe := congrArg (fun v : V => (v : E)) expansion
    simp only [Submodule.coe_sum, Submodule.coe_smul] at coe
    exact coe.symm

/-- The regularized traces of a finite-rank projector converge to its rank. -/
theorem projector_tendsto {ι : Type*} {l : Filter ι} (F : ι → Family E Y)
    (P : E →L[ℂ] E) (idem : P.comp P = P) [FiniteDimensional ℂ (P.range)]
    (weak : ∀ v ∈ P.range, ∀ φ : E →L[ℂ] ℂ,
      Tendsto (fun j => φ ((F j).smoothing v)) l (𝓝 (φ v))) :
    Tendsto (fun j => (F j).traceL P) l (𝓝 (Module.finrank ℂ (P.range) : ℂ)) := by
  obtain ⟨b, c, member, normalized, expansion⟩ := projector_expansion P idem
  have each (j : ι) : (F j).traceL P = ∑ i, c i ((F j).smoothing (b i)) := by
    conv_lhs => rw [expansion]
    rw [map_sum]
    exact sum_congr rfl fun i _ => (F j).traceL_smulRight (c i) (b i)
  have limit : Tendsto (fun j => ∑ i, c i ((F j).smoothing (b i))) l (𝓝 (∑ i, c i (b i))) :=
    tendsto_finsetSum _ fun i _ => weak (b i) (member i) (c i)
  simp only [normalized, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at limit
  exact limit.congr fun j => (each j).symm

/-- Peripheral simplicity from regularized traces. -/
theorem peripheral_rank (A : E →L[ℂ] E) (Γ : Finset ℂ) (unit : ∀ γ ∈ Γ, ‖γ‖ = 1)
    (P : ℂ → E →L[ℂ] E) (idem : ∀ γ ∈ Γ, (P γ).comp (P γ) = P γ)
    (finite : ∀ γ ∈ Γ, FiniteDimensional ℂ ((P γ).range))
    (decomposition : Tendsto (fun k : ℕ => ‖A ^ k - ∑ γ ∈ Γ, γ ^ k • P γ‖) atTop (𝓝 0))
    {ι : Type*} {l : Filter ι} [l.NeBot] (F : ι → Family E Y)
    (weak : ∀ γ ∈ Γ, ∀ v ∈ (P γ).range, ∀ φ : E →L[ℂ] ℂ,
      Tendsto (fun j => φ ((F j).smoothing v)) l (𝓝 (φ v)))
    (t : ℕ → ℂ) (periodic : Tendsto t atTop (𝓝 1)) (δ : ι → ℝ)
    (compare : ∀ j, ∀ᶠ k in atTop, ‖(F j).traceL (A ^ k) - t k‖ ≤ δ j)
    (small : Tendsto δ l (𝓝 0)) :
    ∀ γ ∈ Γ, Module.finrank ℂ ((P γ).range) = if γ = 1 then 1 else 0 := by
  have result := PeripheralTraceRank.multiplicity_eq Γ unit
    (fun j k => (F j).traceL (A ^ k)) (fun j γ => (F j).traceL (P γ))
    (fun γ => (Module.finrank ℂ ((P γ).range) : ℂ)) t δ
    (fun j => by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
        (by simpa only [mul_zero] using decomposition.const_mul ‖(F j).traceL‖)
      have linear : (F j).traceL (A ^ k) - ∑ γ ∈ Γ, (F j).traceL (P γ) * γ ^ k =
          (F j).traceL (A ^ k - ∑ γ ∈ Γ, γ ^ k • P γ) := by
        rw [map_sub, map_sum]
        congr 1
        exact sum_congr rfl fun γ _ => by rw [map_smul, smul_eq_mul, mul_comm]
      rw [linear]
      exact (F j).traceL.le_opNorm _)
    (fun γ hγ => by
      let := finite γ hγ
      exact projector_tendsto F (P γ) (idem γ hγ) (weak γ hγ))
    periodic compare small
  intro γ hγ
  have h := result γ hγ
  by_cases one : γ = 1
  · simp only [one, ↓reduceIte] at h ⊢
    exact_mod_cast h
  · simp only [one, ↓reduceIte] at h ⊢
    exact_mod_cast h

end LeanShared.RegularizedTraceFunctional
