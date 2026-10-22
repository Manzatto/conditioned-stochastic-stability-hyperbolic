module

public import LeanShared.Analysis.AmbientLeafNorm
public import LeanShared.Analysis.SchwartzLeafComponent
public import LeanShared.Analysis.NormCompletionEquivalence

/-!
# Compact Schwartz smoothing in ambient graph measures

The target uses L¹ of the actual pushforward graph measure on the ambient
Euclidean space. Exact norm equality with parameter integration is proved,
and transfers compactness of the constructed fixed-kernel operator. Neither
an ambient norm equivalence nor an ambient compactness certificate is supplied.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped SchwartzMap BoundedContinuousFunction

namespace LeanShared.SchwartzLeafComponent

variable {E I U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]
  {K : Set E} (hK : IsCompact K) (ψ : I → 𝓢(E, ℂ)) (a : I → K →ᵇ ℂ)
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (k : ℕ) (hk : (Module.finrank ℝ U : ℝ) < (k : ℝ))

def ambientSmoothing (u : Source (K := K) (I := I)) :
    GraphLeafNorm.AmbientLeafSpace (E := E) μ (J := J) :=
  GraphLeafNorm.ambientOfDecayingFunction μ hJ hk
    (smoothingFunction hK ψ a u).continuous.measurable
    (mul_nonneg (norm_nonneg u) (sectionDecayConstant_nonneg hK ψ a (2 * k)))
    (GraphLeafNorm.fastDecay_le_slow
      (mul_nonneg (norm_nonneg u) (sectionDecayConstant_nonneg hK ψ a (2 * k)))
      (GraphLeafNorm.exponent_pos hk).le (fun x => by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          smoothingFunction_decay hK ψ a u (2 * k) x))

omit [FiniteDimensional ℝ E] in
theorem ambientSmoothing_ae (u : Source (K := K) (I := I))
    (L : GraphLeafNorm.GraphLeaf U E J) :
    ambientSmoothing hK ψ a μ hJ k hk u L =ᵐ[L.measure μ]
      fun x => u (kernelSection ψ a x) :=
  MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr (GraphLeafNorm.integrable_ambient μ hk
    (smoothingFunction hK ψ a u).continuous.measurable
    (mul_nonneg (norm_nonneg u) (sectionDecayConstant_nonneg hK ψ a (2 * k)))
    (GraphLeafNorm.fastDecay_le_slow
      (mul_nonneg (norm_nonneg u) (sectionDecayConstant_nonneg hK ψ a (2 * k)))
      (GraphLeafNorm.exponent_pos hk).le (fun x => by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          smoothingFunction_decay hK ψ a u (2 * k) x)) L))

theorem norm_ambientSmoothing_eq_source (u : Source (K := K) (I := I)) :
    ‖ambientSmoothing hK ψ a μ hJ k hk u‖ =
      ‖operator hK ψ a μ hJ k hk u‖ :=
  GraphLeafNorm.norm_ambientOfDecayingFunction_eq_source _ _ _ _ _ _

def ambientLinearMap : Source (K := K) (I := I) →ₗ[ℂ]
    GraphLeafNorm.AmbientLeafSpace (E := E) μ (J := J) where
  toFun := ambientSmoothing hK ψ a μ hJ k hk
  map_add' u v := by
    apply lp.ext
    funext L
    change ambientSmoothing hK ψ a μ hJ k hk (u + v) L =
      ambientSmoothing hK ψ a μ hJ k hk u L + ambientSmoothing hK ψ a μ hJ k hk v L
    apply Lp.ext
    filter_upwards [ambientSmoothing_ae hK ψ a μ hJ k hk (u + v) L,
      ambientSmoothing_ae hK ψ a μ hJ k hk u L,
      ambientSmoothing_ae hK ψ a μ hJ k hk v L,
      Lp.coeFn_add (ambientSmoothing hK ψ a μ hJ k hk u L)
        (ambientSmoothing hK ψ a μ hJ k hk v L)] with x huv hu hv hadd
    rw [huv, hadd]
    change (u + v) (kernelSection ψ a x) =
      (ambientSmoothing hK ψ a μ hJ k hk u L) x +
        (ambientSmoothing hK ψ a μ hJ k hk v L) x
    rw [hu, hv]
    rfl
  map_smul' c u := by
    apply lp.ext
    funext L
    change ambientSmoothing hK ψ a μ hJ k hk (c • u) L =
      c • ambientSmoothing hK ψ a μ hJ k hk u L
    apply Lp.ext
    filter_upwards [ambientSmoothing_ae hK ψ a μ hJ k hk (c • u) L,
      ambientSmoothing_ae hK ψ a μ hJ k hk u L,
      Lp.coeFn_smul c (ambientSmoothing hK ψ a μ hJ k hk u L)] with x hcu hu hsmul
    rw [hcu, hsmul]
    change (c • u) (kernelSection ψ a x) =
      c • ((ambientSmoothing hK ψ a μ hJ k hk u L) x)
    rw [hu]
    rfl

def ambientOperator : Source (K := K) (I := I) →L[ℂ]
    GraphLeafNorm.AmbientLeafSpace (E := E) μ (J := J) :=
  (ambientLinearMap hK ψ a μ hJ k hk).mkContinuous ‖operator hK ψ a μ hJ k hk‖
    (fun u => by
      change ‖ambientSmoothing hK ψ a μ hJ k hk u‖ ≤ _
      rw [norm_ambientSmoothing_eq_source]
      exact (operator hK ψ a μ hJ k hk).le_opNorm u)

theorem norm_ambientOperator_eq_source (u : Source (K := K) (I := I)) :
    ‖ambientOperator hK ψ a μ hJ k hk u‖ = ‖operator hK ψ a μ hJ k hk u‖ :=
  norm_ambientSmoothing_eq_source hK ψ a μ hJ k hk u

theorem dist_ambientOperator_eq_source (u v : Source (K := K) (I := I)) :
    dist (ambientOperator hK ψ a μ hJ k hk u) (ambientOperator hK ψ a μ hJ k hk v) =
      dist (operator hK ψ a μ hJ k hk u) (operator hK ψ a μ hJ k hk v) := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub]
  exact norm_ambientOperator_eq_source hK ψ a μ hJ k hk (u - v)

theorem ambientOperator_isCompact : IsCompactOperator (ambientOperator hK ψ a μ hJ k hk) := by
  let s := closedBall (0 : Source (K := K) (I := I)) 1
  let q : ∀ _ : Unit, Source (K := K) (I := I) →
      GraphLeafNorm.LeafSpace (E := E) μ (J := J) := fun _ => operator hK ψ a μ hJ k hk
  have hc := (operator_isCompact hK ψ a μ hJ k hk).isCompact_closure_image_closedBall
    (f := (operator hK ψ a μ hJ k hk).toLinearMap) 1
  apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image _).mpr
  refine ⟨s, closedBall_mem_nhds _ zero_lt_one, ?_⟩
  apply CompactnessFromComponents.isCompact_closure_image_of_controls s
    (ambientOperator hK ψ a μ hJ k hk) q
  intro ε hε
  refine ⟨(), ε, hε, hc.totallyBounded.subset subset_closure, ?_⟩
  intro u _ v _ huv
  rwa [dist_ambientOperator_eq_source]

theorem ambientOperator_ae (u : Source (K := K) (I := I))
    (L : GraphLeafNorm.GraphLeaf U E J) :
    ambientOperator hK ψ a μ hJ k hk u L =ᵐ[L.measure μ]
      fun x => u (kernelSection ψ a x) :=
  ambientSmoothing_ae hK ψ a μ hJ k hk u L

/-- The two constructions give the same completed smoothing range, with
exact core agreement; the norm identity is proved above. -/
def ambientCompletionEquivalence :
    DyadicCompletion.closedCore (operator hK ψ a μ hJ k hk).toLinearMap ≃ₗᵢ[ℂ]
      DyadicCompletion.closedCore (ambientOperator hK ψ a μ hJ k hk).toLinearMap :=
  NormCompletionEquivalence.equivalence _ _
    (fun u => (norm_ambientOperator_eq_source hK ψ a μ hJ k hk u).symm)

@[simp] theorem ambientCompletionEquivalence_core (u : Source (K := K) (I := I)) :
    ambientCompletionEquivalence hK ψ a μ hJ k hk
      (DyadicCompletion.coreLift (operator hK ψ a μ hJ k hk).toLinearMap u) =
        DyadicCompletion.coreLift (ambientOperator hK ψ a μ hJ k hk).toLinearMap u :=
  NormCompletionEquivalence.equivalence_core _ _ _ u

end LeanShared.SchwartzLeafComponent
