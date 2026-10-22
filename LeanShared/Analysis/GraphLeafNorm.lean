module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Graph leaf measures and their uniform integral norm

A graph leaf is parameterized by an injective graph map whose parameter
projection does not increase norm. Its source measure is the restriction of
Haar measure to a measurable domain, weighted by a bounded measurable area
density. The resulting ambient measure is its pushforward. Identifying that
area density with a Riemannian Gram Jacobian is a separate geometric bridge.

The leaf target is the actual complete supremum of the parameterized L¹
spaces. Thus no compactness or small-tail property is built into its definition.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LeanShared.GraphLeafNorm

variable {U E : Type*} [NormedAddCommGroup U] [NormedAddCommGroup E]

/-- A polynomial radial envelope, integrable above the dimension. -/
def radialWeight (r : ℝ) (x : E) : ℝ := (1 + ‖x‖) ^ (-r)

theorem radialWeight_nonneg (r : ℝ) (x : E) : 0 ≤ radialWeight r x := by
  unfold radialWeight
  positivity

theorem radialWeight_le_one {r : ℝ} (hr : 0 ≤ r) (x : E) : radialWeight r x ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by linarith)

theorem radialWeight_antitone_norm {r : ℝ} (hr : 0 ≤ r) {x : E} {y : U}
    (hxy : ‖y‖ ≤ ‖x‖) : radialWeight r x ≤ radialWeight r y := by
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

theorem radialWeight_double (r : ℝ) (x : E) :
    radialWeight (2 * r) x = radialWeight r x * radialWeight r x := by
  unfold radialWeight
  rw [show -(2 * r) = -r + -r by ring, Real.rpow_add (by positivity)]

theorem radialWeight_tail {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (x : E)
    (hx : R ≤ ‖x‖) :
    radialWeight (2 * r) x ≤ (1 + R) ^ (-r) * radialWeight r x := by
  rw [radialWeight_double]
  apply mul_le_mul_of_nonneg_right _ (radialWeight_nonneg r x)
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

variable [MeasurableSpace U] [MeasurableSpace E]

/-- Measurable graph data with a common upper bound on its area density.
The parameter-norm bound is supplied by the graph's projection. -/
structure GraphLeaf (U E : Type*) [NormedAddCommGroup U] [NormedAddCommGroup E]
    [MeasurableSpace U] [MeasurableSpace E] (J : ℝ) where
  domain : Set U
  measurable_domain : MeasurableSet domain
  graph : U → E
  measurable_graph : Measurable graph
  injective_graph : Function.Injective graph
  parameter_norm_le : ∀ u, ‖u‖ ≤ ‖graph u‖
  density : U → ℝ≥0∞
  measurable_density : Measurable density
  density_le : ∀ u, density u ≤ ENNReal.ofReal J

namespace GraphLeaf

/-- A literal measurable graph, with its first-coordinate projection. -/
def ofFunction {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V]
    (h : U → V) (hh : Measurable h) (D : Set U) (hD : MeasurableSet D)
    (ρ : U → ℝ≥0∞) (hρ : Measurable ρ) {J : ℝ}
    (hρJ : ∀ u, ρ u ≤ ENNReal.ofReal J) : GraphLeaf U (U × V) J where
  domain := D
  measurable_domain := hD
  graph := fun u => (u, h u)
  measurable_graph := measurable_id.prodMk hh
  injective_graph := fun _ _ heq => congrArg Prod.fst heq
  parameter_norm_le := fun u => norm_fst_le (u, h u)
  density := ρ
  measurable_density := hρ
  density_le := hρJ

variable {J : ℝ} (L : GraphLeaf U E J) (μ : Measure U)

/-- The actual weighted parameter measure for this leaf. -/
def sourceMeasure : Measure U := (μ.restrict L.domain).withDensity L.density

/-- The actual ambient graph measure. -/
def measure : Measure E := (L.sourceMeasure μ).map L.graph

/-- The source measure is dominated uniformly by `J` times ambient Haar measure. -/
theorem sourceMeasure_le : L.sourceMeasure μ ≤ ENNReal.ofReal J • μ := by
  calc
    L.sourceMeasure μ ≤ (μ.restrict L.domain).withDensity (fun _ => ENNReal.ofReal J) :=
      withDensity_mono (ae_of_all _ L.density_le)
    _ = ENNReal.ofReal J • μ.restrict L.domain := withDensity_const _
    _ ≤ ENNReal.ofReal J • μ := by
      intro s
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_right (Measure.restrict_le_self (s := L.domain) s) _

theorem integral_measure (f : E → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂L.measure μ) = ∫ u, f (L.graph u) ∂L.sourceMeasure μ :=
  integral_map_of_stronglyMeasurable L.measurable_graph hf.stronglyMeasurable

variable [BorelSpace U] [BorelSpace E]

omit [BorelSpace U] in
/-- Uniform finite-ball volume bound for the actual ambient graph measure. -/
theorem measure_closedBall_le (R : ℝ) :
    L.measure μ (Metric.closedBall (0 : E) R) ≤
      ENNReal.ofReal J * μ (Metric.closedBall (0 : U) R) := by
  rw [measure, Measure.map_apply L.measurable_graph measurableSet_closedBall]
  calc
    _ ≤ (ENNReal.ofReal J • μ) (L.graph ⁻¹' Metric.closedBall (0 : E) R) :=
      L.sourceMeasure_le μ _
    _ = ENNReal.ofReal J * μ (L.graph ⁻¹' Metric.closedBall (0 : E) R) := by
      rw [Measure.smul_apply, smul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul_right
      apply measure_mono
      intro u hu
      have hh : ‖L.graph u‖ ≤ R := mem_closedBall_zero_iff.mp hu
      exact mem_closedBall_zero_iff.mpr ((L.parameter_norm_le u).trans hh)

end GraphLeaf

section Haar

variable [BorelSpace U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J r : ℝ}
  (hJ : 0 ≤ J) (hr : (Module.finrank ℝ U : ℝ) < r)

omit [MeasurableSpace U] [BorelSpace U] [FiniteDimensional ℝ U] in
theorem exponent_pos (hr : (Module.finrank ℝ U : ℝ) < r) : 0 < r :=
  lt_of_le_of_lt (by positivity) hr

include hr in
theorem integrable_radialWeight : Integrable (radialWeight r : U → ℝ) μ :=
  integrable_one_add_norm hr

include hr in
theorem integrable_source_radialWeight (L : GraphLeaf U E J) :
    Integrable (radialWeight r : U → ℝ) (L.sourceMeasure μ) :=
  ((integrable_radialWeight μ hr).smul_measure ENNReal.ofReal_ne_top).mono_measure
    (L.sourceMeasure_le μ)

include hJ hr in
/-- A common explicit bound for the integral envelope on every graph. -/
theorem integral_source_radialWeight_le (L : GraphLeaf U E J) :
    (∫ u, radialWeight r u ∂L.sourceMeasure μ) ≤ J * ∫ u, radialWeight r u ∂μ := by
  calc
    _ ≤ ∫ u, radialWeight r u ∂(ENNReal.ofReal J • μ) :=
      integral_mono_measure (L.sourceMeasure_le μ)
        (ae_of_all _ (radialWeight_nonneg r))
        ((integrable_radialWeight μ hr).smul_measure ENNReal.ofReal_ne_top)
    _ = _ := by rw [integral_smul_measure, ENNReal.toReal_ofReal hJ, smul_eq_mul]

variable {f : E → ℂ} (hf : Measurable f) {A : ℝ} (hA : 0 ≤ A)
    (hdecay : ∀ x, ‖f x‖ ≤ A * radialWeight r x)

include hr hf hA hdecay in
/-- Actual graph pullbacks of polynomially decaying functions belong to L¹. -/
theorem integrable_graph (L : GraphLeaf U E J) :
    Integrable (fun u => f (L.graph u)) (L.sourceMeasure μ) := by
  apply ((integrable_source_radialWeight μ hr L).const_mul A).mono'
    (hf.comp L.measurable_graph).aestronglyMeasurable
  exact ae_of_all _ fun u => (hdecay _).trans (mul_le_mul_of_nonneg_left
    (radialWeight_antitone_norm (exponent_pos hr).le (L.parameter_norm_le u)) hA)

include hr hJ hf hA hdecay in
theorem integral_graph_norm_le (L : GraphLeaf U E J) :
    (∫ u, ‖f (L.graph u)‖ ∂L.sourceMeasure μ) ≤ A * J * ∫ u, radialWeight r u ∂μ := by
  calc
    _ ≤ ∫ u, A * radialWeight r u ∂L.sourceMeasure μ :=
      integral_mono_ae (integrable_graph μ hr hf hA hdecay L).norm
        ((integrable_source_radialWeight μ hr L).const_mul A)
        (ae_of_all _ fun u => (hdecay _).trans (mul_le_mul_of_nonneg_left
          (radialWeight_antitone_norm (exponent_pos hr).le (L.parameter_norm_le u)) hA))
    _ = A * ∫ u, radialWeight r u ∂L.sourceMeasure μ := integral_const_mul _ _
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (integral_source_radialWeight_le μ hJ hr L) hA

/-- The complete actual supremum-L¹ target over all graphs with the density bound. -/
abbrev LeafSpace := lp (fun L : GraphLeaf U E J => Lp ℂ 1 (L.sourceMeasure μ)) ∞

/-- Represent a genuinely integrable decaying function in all leaf L¹ spaces. -/
def ofDecayingFunction : LeafSpace (E := E) μ (J := J) := by
  let v := fun L : GraphLeaf U E J =>
    (memLp_one_iff_integrable.mpr (integrable_graph μ hr hf hA hdecay L)).toLp
      (fun u => f (L.graph u))
  refine ⟨v, memℓp_infty ?_⟩
  refine ⟨A * J * ∫ u, radialWeight r u ∂μ, ?_⟩
  rintro _ ⟨L, rfl⟩
  change ‖(memLp_one_iff_integrable.mpr (integrable_graph μ hr hf hA hdecay L)).toLp
      (fun u => f (L.graph u))‖ ≤ _
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ u, ‖f (L.graph u)‖ ∂L.sourceMeasure μ :=
      integral_congr_ae ((MemLp.coeFn_toLp _).fun_comp Norm.norm)
    _ ≤ _ := integral_graph_norm_le μ hJ hr hf hA hdecay L

theorem ofDecayingFunction_apply (L : GraphLeaf U E J) :
    ofDecayingFunction μ (hJ := hJ) (hr := hr) (hf := hf) (hA := hA) (hdecay := hdecay) L =
      (memLp_one_iff_integrable.mpr (integrable_graph μ hr hf hA hdecay L)).toLp
        (fun u => f (L.graph u)) := rfl

theorem norm_ofDecayingFunction_le :
    ‖ofDecayingFunction μ (hJ := hJ) (hr := hr) (hf := hf) (hA := hA) (hdecay := hdecay)‖ ≤
      A * J * ∫ u, radialWeight r u ∂μ := by
  apply lp.norm_le_of_forall_le (by
    exact mul_nonneg (mul_nonneg hA hJ) (integral_nonneg (radialWeight_nonneg r)))
  intro L
  rw [ofDecayingFunction_apply, L1.norm_eq_integral_norm]
  calc
    _ = ∫ u, ‖f (L.graph u)‖ ∂L.sourceMeasure μ :=
      integral_congr_ae ((MemLp.coeFn_toLp _).fun_comp Norm.norm)
    _ ≤ _ := integral_graph_norm_le μ hJ hr hf hA hdecay L

omit [MeasurableSpace E] in
/-- A faster envelope supplies the integrable slower envelope. -/
theorem fastDecay_le_slow {f : E → ℂ} {A r : ℝ} (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hfast : ∀ x, ‖f x‖ ≤ A * radialWeight (2 * r) x) :
    ∀ x, ‖f x‖ ≤ A * radialWeight r x := by
  intro x
  apply (hfast x).trans
  apply mul_le_mul_of_nonneg_left _ hA
  rw [radialWeight_double]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (radialWeight_le_one hr x)
    (radialWeight_nonneg r x)

end Haar

section LocalControl

variable [BorelSpace U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J r A : ℝ}
  (hJ : 0 ≤ J) (hr : (Module.finrank ℝ U : ℝ) < r) (hA : 0 ≤ A)
  {f g : E → ℂ} (hf : Measurable f) (hg : Measurable g)
  (hfastf : ∀ x, ‖f x‖ ≤ A * radialWeight (2 * r) x)
  (hfastg : ∀ x, ‖g x‖ ≤ A * radialWeight (2 * r) x)

/-- The finite-volume parameter-ball envelope. -/
def localEnvelope (R : ℝ) (u : U) : ℝ :=
  (Metric.closedBall (0 : U) R).indicator (fun _ => 1) u

omit [MeasurableSpace U] [BorelSpace U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] in
theorem localEnvelope_nonneg (R : ℝ) (u : U) : 0 ≤ localEnvelope R u :=
  indicator_nonneg (fun _ _ => zero_le_one) _

theorem integrable_localEnvelope (R : ℝ) : Integrable (localEnvelope R : U → ℝ) μ := by
  apply (integrable_indicator_iff measurableSet_closedBall).mpr
  exact integrableOn_const (C := (1 : ℝ))
    (isCompact_closedBall (0 : U) R).measure_lt_top.ne

omit [NormedSpace ℝ U] [FiniteDimensional ℝ U] [μ.IsAddHaarMeasure] in
theorem integral_localEnvelope (R : ℝ) :
    (∫ u, localEnvelope R u ∂μ) = (μ (Metric.closedBall (0 : U) R)).toReal := by
  simp only [localEnvelope, integral_indicator_const _ measurableSet_closedBall,
    smul_eq_mul, mul_one, Measure.real]

theorem integrable_source_localEnvelope (L : GraphLeaf U E J) (R : ℝ) :
    Integrable (localEnvelope R : U → ℝ) (L.sourceMeasure μ) :=
  ((integrable_localEnvelope μ R).smul_measure ENNReal.ofReal_ne_top).mono_measure
    (L.sourceMeasure_le μ)

include hJ in
theorem integral_source_localEnvelope_le (L : GraphLeaf U E J) (R : ℝ) :
    (∫ u, localEnvelope R u ∂L.sourceMeasure μ) ≤
      J * (μ (Metric.closedBall (0 : U) R)).toReal := by
  calc
    _ ≤ ∫ u, localEnvelope R u ∂(ENNReal.ofReal J • μ) :=
      integral_mono_measure (L.sourceMeasure_le μ)
        (ae_of_all _ (localEnvelope_nonneg R))
        ((integrable_localEnvelope μ R).smul_measure ENNReal.ofReal_ne_top)
    _ = _ := by rw [integral_smul_measure, ENNReal.toReal_ofReal hJ, smul_eq_mul,
      integral_localEnvelope]

include hr hA hfastf hfastg in
omit [BorelSpace U] [FiniteDimensional ℝ U] in
/-- Local uniform closeness plus genuine radial decay controls every graph's
pullback pointwise, with a common explicit tail. -/
theorem graph_difference_bound (L : GraphLeaf U E J) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hclose : ∀ x, ‖x‖ ≤ R → ‖f x - g x‖ ≤ δ) (u : U) :
    ‖f (L.graph u) - g (L.graph u)‖ ≤ δ * localEnvelope R u +
      (2 * A * (1 + R) ^ (-r)) * radialWeight r u := by
  have hr0 := (exponent_pos hr).le
  have hpow : 0 ≤ (1 + R) ^ (-r) := Real.rpow_nonneg (by linarith) _
  by_cases hin : ‖L.graph u‖ ≤ R
  · have hu : u ∈ Metric.closedBall (0 : U) R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (L.parameter_norm_le u).trans hin
    rw [localEnvelope, indicator_of_mem hu, mul_one]
    exact (hclose _ hin).trans (le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) hpow) (radialWeight_nonneg r u)))
  · have hnorm : ‖f (L.graph u) - g (L.graph u)‖ ≤
        2 * A * radialWeight (2 * r) (L.graph u) := by
      have hh := norm_sub_le (f (L.graph u)) (g (L.graph u))
      linarith [hfastf (L.graph u), hfastg (L.graph u)]
    have htail := radialWeight_tail hr0 hR (L.graph u) (le_of_not_ge hin)
    have hbase := radialWeight_antitone_norm hr0 (L.parameter_norm_le u)
    have hb : ‖f (L.graph u) - g (L.graph u)‖ ≤
        (2 * A * (1 + R) ^ (-r)) * radialWeight r u := calc
      _ ≤ 2 * A * radialWeight (2 * r) (L.graph u) := hnorm
      _ ≤ 2 * A * ((1 + R) ^ (-r) * radialWeight r (L.graph u)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hbase (by positivity)
    exact hb.trans (le_add_of_nonneg_left (mul_nonneg hδ (localEnvelope_nonneg R u)))

include hJ hr hA hf hg hfastf hfastg in
/-- The actual supremum of leaf L¹ distances is controlled by local uniform
distance and an explicit tail tending to zero. -/
theorem norm_sub_ofDecayingFunction_le {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hclose : ∀ x, ‖x‖ ≤ R → ‖f x - g x‖ ≤ δ) :
    ‖ofDecayingFunction μ (hJ := hJ) (hr := hr) (hf := hf) (hA := hA)
        (hdecay := fastDecay_le_slow hA (exponent_pos hr).le hfastf) -
      ofDecayingFunction μ (hJ := hJ) (hr := hr) (hf := hg) (hA := hA)
        (hdecay := fastDecay_le_slow hA (exponent_pos hr).le hfastg)‖ ≤
      δ * J * (μ (Metric.closedBall (0 : U) R)).toReal +
        (2 * A * (1 + R) ^ (-r)) * J * ∫ u, radialWeight r u ∂μ := by
  have htail0 : 0 ≤ 2 * A * (1 + R) ^ (-r) := by positivity
  apply lp.norm_le_of_forall_le (add_nonneg (by positivity)
    (mul_nonneg (mul_nonneg htail0 hJ) (integral_nonneg (radialWeight_nonneg r))))
  intro L
  let hif := integrable_graph μ hr hf hA (fastDecay_le_slow hA (exponent_pos hr).le hfastf) L
  let hig := integrable_graph μ hr hg hA (fastDecay_le_slow hA (exponent_pos hr).le hfastg) L
  change ‖(memLp_one_iff_integrable.mpr hif).toLp (fun u => f (L.graph u)) -
      (memLp_one_iff_integrable.mpr hig).toLp (fun u => g (L.graph u))‖ ≤ _
  rw [← MemLp.toLp_sub, L1.norm_eq_integral_norm]
  have heq : (∫ u, ‖(memLp_one_iff_integrable.mpr hif).sub
      (memLp_one_iff_integrable.mpr hig) |>.toLp
      ((fun u => f (L.graph u)) - fun u => g (L.graph u)) u‖ ∂L.sourceMeasure μ) =
      ∫ u, ‖f (L.graph u) - g (L.graph u)‖ ∂L.sourceMeasure μ := by
    exact integral_congr_ae ((MemLp.coeFn_toLp _).fun_comp Norm.norm)
  rw [heq]
  calc
    _ ≤ ∫ u, δ * localEnvelope R u +
        (2 * A * (1 + R) ^ (-r)) * radialWeight r u ∂L.sourceMeasure μ :=
      integral_mono_ae (hif.sub hig).norm
        (((integrable_source_localEnvelope μ L R).const_mul δ).add
          ((integrable_source_radialWeight μ hr L).const_mul _))
        (ae_of_all _ (graph_difference_bound hr hA hfastf hfastg L hR hδ hclose))
    _ = δ * (∫ u, localEnvelope R u ∂L.sourceMeasure μ) +
        (2 * A * (1 + R) ^ (-r)) * ∫ u, radialWeight r u ∂L.sourceMeasure μ := by
      rw [integral_add ((integrable_source_localEnvelope μ L R).const_mul δ)
        ((integrable_source_radialWeight μ hr L).const_mul _), integral_const_mul,
        integral_const_mul]
    _ ≤ _ := by
      simpa only [mul_assoc] using add_le_add
        (mul_le_mul_of_nonneg_left (integral_source_localEnvelope_le μ hJ L R) hδ)
        (mul_le_mul_of_nonneg_left (integral_source_radialWeight_le μ hJ hr L) htail0)

end LocalControl

end LeanShared.GraphLeafNorm
