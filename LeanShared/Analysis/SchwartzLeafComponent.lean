module

public import LeanShared.Analysis.SchwartzKernelBounds
public import LeanShared.Analysis.DecayingFunctionCompactness
public import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Genuine fixed Schwartz smoothing components in graph-leaf L¹

Finitely many fixed translated Schwartz kernels, multiplied by fixed bounded
continuous compact-source coefficients, are paired with a bounded linear
functional on their finite tuple space. All decay and equicontinuity estimates
are derived from the Schwartz kernels. Component compactness is a conclusion.
Identifying these finite tuple functionals with the manuscript's supported
finite-order distributions is a later distribution/jet representation bridge.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped SchwartzMap BoundedContinuousFunction ENNReal NNReal

namespace LeanShared.SchwartzLeafComponent

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
  {K : Set E} (hK : IsCompact K) (ψ : I → 𝓢(E, ℂ)) (a : I → K →ᵇ ℂ)

/-- The actual finite tuple of compact-source translated kernels. -/
def kernelSection (x : E) : I → K →ᵇ ℂ := fun i =>
  ((ψ i).toBoundedContinuousFunction.compContinuous
    ⟨fun y : K => x - y.val, continuous_const.sub continuous_subtype_val⟩) * a i

omit [Fintype I] in
theorem kernelSection_apply (x : E) (i : I) (y : K) :
    kernelSection ψ a x i y = ψ i (x - y.val) * a i y := rfl

include hK in
/-- Actual Schwartz decay, uniform over the finite tuple and compact translations. -/
theorem exists_kernelSection_decay (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, ‖kernelSection ψ a x‖ ≤
      A * GraphLeafNorm.radialWeight (m : ℝ) x := by
  classical
  choose A hA hb using fun i =>
    SchwartzKernelBounds.exists_uniform_translated_decay (ψ i) hK m
  let C := ∑ i, A i * ‖a i‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => mul_nonneg (hA i) (norm_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (GraphLeafNorm.radialWeight_nonneg _ _))).mpr
  intro i
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg hC (GraphLeafNorm.radialWeight_nonneg _ _))).mpr
  intro y
  rw [kernelSection_apply, norm_mul]
  have hi : A i * ‖a i‖ ≤ C := Finset.single_le_sum
    (fun j _ => mul_nonneg (hA j) (norm_nonneg _)) (Finset.mem_univ i)
  calc
    _ ≤ (A i * GraphLeafNorm.radialWeight (m : ℝ) x) * ‖a i‖ :=
      mul_le_mul (hb i x y.val y.property) ((a i).norm_coe_le_norm y)
        (norm_nonneg _) (mul_nonneg (hA i) (GraphLeafNorm.radialWeight_nonneg _ _))
    _ = (A i * ‖a i‖) * GraphLeafNorm.radialWeight (m : ℝ) x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hi (GraphLeafNorm.radialWeight_nonneg _ _)

/-- The section is globally Lipschitz; the finite coefficient tuple is fixed. -/
theorem exists_kernelSection_lipschitz :
    ∃ L : ℝ≥0, LipschitzWith L (kernelSection ψ a) := by
  classical
  choose L hL using fun i => SchwartzKernelBounds.exists_lipschitz (ψ i)
  let C : ℝ := ∑ i, (L i : ℝ) * ‖a i‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => mul_nonneg (L i).coe_nonneg (norm_nonneg _)
  refine ⟨⟨C, hC⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC dist_nonneg)).mpr
  intro i
  apply (BoundedContinuousFunction.norm_le (mul_nonneg hC dist_nonneg)).mpr
  intro z
  change ‖ψ i (x - z.val) * a i z - ψ i (y - z.val) * a i z‖ ≤ C * dist x y
  rw [← sub_mul, norm_mul]
  have hk : ‖ψ i (x - z.val) - ψ i (y - z.val)‖ ≤ (L i : ℝ) * dist x y := by
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using
      (hL i).dist_le_mul (x - z.val) (y - z.val)
  have hi : (L i : ℝ) * ‖a i‖ ≤ C := Finset.single_le_sum
    (fun j _ => mul_nonneg (L j).coe_nonneg (norm_nonneg _)) (Finset.mem_univ i)
  calc
    _ ≤ ((L i : ℝ) * dist x y) * ‖a i‖ :=
      mul_le_mul hk ((a i).norm_coe_le_norm z) (norm_nonneg _) (by positivity)
    _ = ((L i : ℝ) * ‖a i‖) * dist x y := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hi dist_nonneg

/-- The actual bounded functional source for the finite kernel/jet tuple. -/
abbrev Source := (I → K →ᵇ ℂ) →L[ℂ] ℂ

def sectionDecayConstant (m : ℕ) : ℝ := (exists_kernelSection_decay hK ψ a m).choose

theorem sectionDecayConstant_nonneg (m : ℕ) : 0 ≤ sectionDecayConstant hK ψ a m :=
  (exists_kernelSection_decay hK ψ a m).choose_spec.1

theorem kernelSection_decay (m : ℕ) (x : E) :
    ‖kernelSection ψ a x‖ ≤ sectionDecayConstant hK ψ a m *
      GraphLeafNorm.radialWeight (m : ℝ) x :=
  (exists_kernelSection_decay hK ψ a m).choose_spec.2 x

def sectionLipschitzConstant : ℝ≥0 := (exists_kernelSection_lipschitz ψ a).choose

theorem kernelSection_lipschitz :
    LipschitzWith (sectionLipschitzConstant ψ a) (kernelSection ψ a) :=
  (exists_kernelSection_lipschitz ψ a).choose_spec

/-- The actual smoothing output, obtained by pairing with the translated kernels. -/
def smoothingFunction (u : Source (K := K) (I := I)) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => u (kernelSection ψ a x))
    (u.continuous.comp (kernelSection_lipschitz ψ a).continuous)
    (‖u‖ * sectionDecayConstant hK ψ a 0)
    (fun x => by
      apply (u.le_opNorm (kernelSection ψ a x)).trans
      have hh := kernelSection_decay hK ψ a 0 x
      simp only [GraphLeafNorm.radialWeight, Nat.cast_zero, neg_zero, Real.rpow_zero,
        mul_one] at hh
      exact mul_le_mul_of_nonneg_left hh (norm_nonneg u))

theorem smoothingFunction_apply (u : Source (K := K) (I := I)) (x : E) :
    smoothingFunction hK ψ a u x = u (kernelSection ψ a x) := rfl

theorem smoothingFunction_decay (u : Source (K := K) (I := I)) (m : ℕ) (x : E) :
    ‖smoothingFunction hK ψ a u x‖ ≤ (‖u‖ * sectionDecayConstant hK ψ a m) *
      GraphLeafNorm.radialWeight (m : ℝ) x := by
  calc
    _ ≤ ‖u‖ * ‖kernelSection ψ a x‖ := u.le_opNorm _
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (kernelSection_decay hK ψ a m x) (norm_nonneg u)

theorem smoothingFunction_lipschitz (u : Source (K := K) (I := I)) :
    LipschitzWith (‖u‖₊ * sectionLipschitzConstant ψ a) (smoothingFunction hK ψ a u) :=
  u.lipschitzWith.comp (kernelSection_lipschitz ψ a)

section Leaves

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (k : ℕ) (hk : (Module.finrank ℝ U : ℝ) < (k : ℝ))

/-- The genuinely constructed smoothing component in the actual leaf L¹ space. -/
def leafSmoothing (u : Source (K := K) (I := I)) : GraphLeafNorm.LeafSpace (E := E) μ (J := J) :=
  GraphLeafNorm.ofDecayingFunction μ (hJ := hJ) (hr := hk)
    (hf := (smoothingFunction hK ψ a u).continuous.measurable)
    (hA := mul_nonneg (norm_nonneg u) (sectionDecayConstant_nonneg hK ψ a (2 * k)))
    (hdecay := GraphLeafNorm.fastDecay_le_slow
      (mul_nonneg (norm_nonneg u) (sectionDecayConstant_nonneg hK ψ a (2 * k)))
      (GraphLeafNorm.exponent_pos hk).le (fun x => by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          smoothingFunction_decay hK ψ a u (2 * k) x))

omit [FiniteDimensional ℝ E] in
theorem leafSmoothing_ae (u : Source (K := K) (I := I))
    (L : GraphLeafNorm.GraphLeaf U E J) :
    leafSmoothing hK ψ a μ hJ k hk u L =ᵐ[L.sourceMeasure μ]
      (fun y => u (kernelSection ψ a (L.graph y))) := by
  let hnonneg := mul_nonneg (norm_nonneg u) (sectionDecayConstant_nonneg hK ψ a (2 * k))
  have hfast : ∀ x, ‖smoothingFunction hK ψ a u x‖ ≤
      (‖u‖ * sectionDecayConstant hK ψ a (2 * k)) *
        GraphLeafNorm.radialWeight (2 * (k : ℝ)) x := by
    intro x
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      smoothingFunction_decay hK ψ a u (2 * k) x
  let hi := GraphLeafNorm.integrable_graph μ hk
    (smoothingFunction hK ψ a u).continuous.measurable hnonneg
    (GraphLeafNorm.fastDecay_le_slow hnonneg (GraphLeafNorm.exponent_pos hk).le hfast) L
  exact MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hi)

/-- A genuine fixed-kernel component is compact in the leaf norm. Its
uniform radial decay and equicontinuity are derived, not assumed. -/
theorem isCompactOperator_leafSmoothing :
    IsCompactOperator (leafSmoothing hK ψ a μ hJ k hk) := by
  let S := closedBall (0 : Source (K := K) (I := I)) 1
  let f : S → E →ᵇ ℂ := fun u => smoothingFunction hK ψ a u.val
  let A := sectionDecayConstant hK ψ a (2 * k)
  have hA : 0 ≤ A := sectionDecayConstant_nonneg hK ψ a (2 * k)
  have hfast : ∀ u x, ‖f u x‖ ≤ A * GraphLeafNorm.radialWeight (2 * (k : ℝ)) x := by
    intro u x
    have hun : ‖u.val‖ ≤ 1 := mem_closedBall_zero_iff.mp u.property
    have hh := smoothingFunction_decay hK ψ a u.val (2 * k) x
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hh
    apply hh.trans
    have hcoef : ‖u.val‖ * A ≤ A := by nlinarith
    exact mul_le_mul_of_nonneg_right hcoef (GraphLeafNorm.radialWeight_nonneg _ _)
  have hcommon : ∀ u : S, LipschitzWith (sectionLipschitzConstant ψ a) (f u) := by
    intro u
    have hun : ‖u.val‖ ≤ 1 := mem_closedBall_zero_iff.mp u.property
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hh := (smoothingFunction_lipschitz hK ψ a u.val).dist_le_mul x y
    simp only [NNReal.coe_mul, coe_nnnorm] at hh
    apply hh.trans
    have hcoef : ‖u.val‖ * (sectionLipschitzConstant ψ a : ℝ) ≤
        (sectionLipschitzConstant ψ a : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hun
        (sectionLipschitzConstant ψ a).coe_nonneg
    exact mul_le_mul_of_nonneg_right hcoef dist_nonneg
  have H := (LipschitzWith.uniformEquicontinuous (fun u x => f u x)
    (sectionLipschitzConstant ψ a) hcommon).equicontinuous
  have hc := GraphLeafNorm.isCompact_closure_leafFamily μ hJ hk hA f hfast H
  have heq : leafSmoothing hK ψ a μ hJ k hk '' S =
      Set.range (GraphLeafNorm.leafFamily μ hJ hk hA f hfast) := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u.val, u.property, rfl⟩
  apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image _).mpr
  refine ⟨S, closedBall_mem_nhds _ zero_lt_one, ?_⟩
  rwa [heq]

/-- The smoothing component is linear in the distribution/tuple functional. -/
def leafSmoothingLinearMap : Source (K := K) (I := I) →ₗ[ℂ]
    GraphLeafNorm.LeafSpace (E := E) μ (J := J) where
  toFun := leafSmoothing hK ψ a μ hJ k hk
  map_add' u v := by
    apply lp.ext
    funext L
    change leafSmoothing hK ψ a μ hJ k hk (u + v) L =
      leafSmoothing hK ψ a μ hJ k hk u L + leafSmoothing hK ψ a μ hJ k hk v L
    apply Lp.ext
    filter_upwards [leafSmoothing_ae hK ψ a μ hJ k hk (u + v) L,
      leafSmoothing_ae hK ψ a μ hJ k hk u L,
      leafSmoothing_ae hK ψ a μ hJ k hk v L,
      Lp.coeFn_add (leafSmoothing hK ψ a μ hJ k hk u L)
        (leafSmoothing hK ψ a μ hJ k hk v L)] with y huv hu hv hadd
    rw [huv, hadd]
    change (u + v) (kernelSection ψ a (L.graph y)) =
      (leafSmoothing hK ψ a μ hJ k hk u L) y +
        (leafSmoothing hK ψ a μ hJ k hk v L) y
    rw [hu, hv]
    rfl
  map_smul' c u := by
    apply lp.ext
    funext L
    change leafSmoothing hK ψ a μ hJ k hk (c • u) L =
      c • leafSmoothing hK ψ a μ hJ k hk u L
    apply Lp.ext
    filter_upwards [leafSmoothing_ae hK ψ a μ hJ k hk (c • u) L,
      leafSmoothing_ae hK ψ a μ hJ k hk u L,
      Lp.coeFn_smul c (leafSmoothing hK ψ a μ hJ k hk u L)] with y hcu hu hsmul
    rw [hcu, hsmul]
    change (c • u) (kernelSection ψ a (L.graph y)) =
      c • ((leafSmoothing hK ψ a μ hJ k hk u L) y)
    rw [hu]
    rfl

/-- Compactness supplies continuity of the constructed linear component. -/
def operator : Source (K := K) (I := I) →L[ℂ]
    GraphLeafNorm.LeafSpace (E := E) μ (J := J) :=
  ContinuousLinearMap.mkOfIsCompactOperator
    (f := leafSmoothingLinearMap hK ψ a μ hJ k hk)
    (isCompactOperator_leafSmoothing hK ψ a μ hJ k hk)

theorem operator_isCompact : IsCompactOperator (operator hK ψ a μ hJ k hk) :=
  isCompactOperator_leafSmoothing hK ψ a μ hJ k hk

theorem operator_ae (u : Source (K := K) (I := I))
    (L : GraphLeafNorm.GraphLeaf U E J) :
    operator hK ψ a μ hJ k hk u L =ᵐ[L.sourceMeasure μ]
      (fun y => u (kernelSection ψ a (L.graph y))) :=
  leafSmoothing_ae hK ψ a μ hJ k hk u L

end Leaves

end LeanShared.SchwartzLeafComponent
