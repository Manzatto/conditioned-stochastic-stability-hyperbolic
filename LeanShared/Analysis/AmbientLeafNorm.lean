module

public import LeanShared.Analysis.DecayingFunctionCompactness

/-!
# Ambient graph-leaf L¹ and the parameter norm

The complete target uses the actual pushforward graph measures on the
ambient space. For common measurable functions its norm and distance agree
exactly with the parameter-space leaf norm. Compactness therefore transfers
without assuming a norm-equivalence certificate. A geometric area identity
can later identify these pushforwards with induced Riemannian leaf volume.
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal BoundedContinuousFunction

namespace LeanShared.GraphLeafNorm

variable {U E : Type*} [NormedAddCommGroup U] [NormedAddCommGroup E]
  [MeasurableSpace U] [MeasurableSpace E]
  {J : ℝ}

abbrev AmbientLeafSpace (μ : Measure U) :=
  lp (fun L : GraphLeaf U E J => Lp ℂ 1 (L.measure μ)) ∞

theorem norm_toLp_ambient_eq_source (L : GraphLeaf U E J) (μ : Measure U)
    (f : E → ℂ) (hf : Measurable f)
    (hm : MemLp f 1 (L.measure μ))
    (hs : MemLp (fun u => f (L.graph u)) 1 (L.sourceMeasure μ)) :
    ‖hm.toLp f‖ = ‖hs.toLp (fun u => f (L.graph u))‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  congr 1
  exact eLpNorm_map_measure hf.aestronglyMeasurable L.measurable_graph.aemeasurable

theorem norm_sub_toLp_ambient_eq_source (L : GraphLeaf U E J) (μ : Measure U)
    (f g : E → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hmf : MemLp f 1 (L.measure μ)) (hmg : MemLp g 1 (L.measure μ))
    (hsf : MemLp (fun u => f (L.graph u)) 1 (L.sourceMeasure μ))
    (hsg : MemLp (fun u => g (L.graph u)) 1 (L.sourceMeasure μ)) :
    ‖hmf.toLp f - hmg.toLp g‖ =
      ‖hsf.toLp (fun u => f (L.graph u)) - hsg.toLp (fun u => g (L.graph u))‖ := by
  rw [← hmf.toLp_sub hmg, ← hsf.toLp_sub hsg]
  exact norm_toLp_ambient_eq_source L μ (f - g) (hf.sub hg) (hmf.sub hmg) (hsf.sub hsg)

section Haar

variable [BorelSpace U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {r A : ℝ}
  (hJ : 0 ≤ J) (hr : (Module.finrank ℝ U : ℝ) < r)
  {f : E → ℂ} (hf : Measurable f) (hA : 0 ≤ A)
  (hdecay : ∀ x, ‖f x‖ ≤ A * radialWeight r x)

include hr hf hA hdecay in
theorem integrable_ambient (L : GraphLeaf U E J) : Integrable f (L.measure μ) :=
  (integrable_map_measure hf.aestronglyMeasurable L.measurable_graph.aemeasurable).mpr
    (integrable_graph μ hr hf hA hdecay L)

/-- The same decaying ambient function in all genuine ambient graph L¹ spaces. -/
def ambientOfDecayingFunction : AmbientLeafSpace (E := E) μ (J := J) := by
  let v := fun L : GraphLeaf U E J =>
    (memLp_one_iff_integrable.mpr (integrable_ambient μ hr hf hA hdecay L)).toLp f
  refine ⟨v, memℓp_infty ?_⟩
  refine ⟨A * J * ∫ u, radialWeight r u ∂μ, ?_⟩
  rintro _ ⟨L, rfl⟩
  change ‖(memLp_one_iff_integrable.mpr (integrable_ambient μ hr hf hA hdecay L)).toLp f‖ ≤ _
  rw [norm_toLp_ambient_eq_source L μ f hf _
    (memLp_one_iff_integrable.mpr (integrable_graph μ hr hf hA hdecay L))]
  exact (lp.norm_apply_le_norm ENNReal.top_ne_zero
    (ofDecayingFunction μ (hJ := hJ) (hr := hr) (hf := hf) (hA := hA) (hdecay := hdecay)) L).trans
    (norm_ofDecayingFunction_le μ hJ hr hf hA hdecay)

theorem ambientOfDecayingFunction_apply (L : GraphLeaf U E J) :
    ambientOfDecayingFunction μ hJ hr hf hA hdecay L =
      (memLp_one_iff_integrable.mpr (integrable_ambient μ hr hf hA hdecay L)).toLp f := rfl

theorem norm_ambientOfDecayingFunction_eq_source :
    ‖ambientOfDecayingFunction μ hJ hr hf hA hdecay‖ =
      ‖ofDecayingFunction μ (hJ := hJ) (hr := hr) (hf := hf) (hA := hA) (hdecay := hdecay)‖ := by
  rw [lp.norm_eq_ciSup, lp.norm_eq_ciSup]
  congr 1
  funext L
  change ‖(memLp_one_iff_integrable.mpr (integrable_ambient μ hr hf hA hdecay L)).toLp f‖ =
    ‖(memLp_one_iff_integrable.mpr (integrable_graph μ hr hf hA hdecay L)).toLp
      (fun u => f (L.graph u))‖
  exact norm_toLp_ambient_eq_source L μ f hf
    (memLp_one_iff_integrable.mpr (integrable_ambient μ hr hf hA hdecay L))
    (memLp_one_iff_integrable.mpr (integrable_graph μ hr hf hA hdecay L))

variable [BorelSpace E] {I : Type*} (F : I → E →ᵇ ℂ)
  (hfast : ∀ i x, ‖F i x‖ ≤ A * radialWeight (2 * r) x)

def ambientLeafFamily (i : I) : AmbientLeafSpace (E := E) μ (J := J) :=
  ambientOfDecayingFunction μ hJ hr (F i).continuous.measurable hA
    (fastDecay_le_slow hA (exponent_pos hr).le (hfast i))

omit hf hdecay in
theorem dist_ambientLeafFamily_eq_source (i j : I) :
    dist (ambientLeafFamily μ hJ hr hA F hfast i) (ambientLeafFamily μ hJ hr hA F hfast j) =
      dist (leafFamily μ hJ hr hA F hfast i) (leafFamily μ hJ hr hA F hfast j) := by
  rw [dist_eq_norm, dist_eq_norm, lp.norm_eq_ciSup, lp.norm_eq_ciSup]
  congr 1
  funext L
  let hd (i : I) := fastDecay_le_slow hA (exponent_pos hr).le (hfast i)
  let hm (i : I) := memLp_one_iff_integrable.mpr
    (integrable_ambient μ hr (F i).continuous.measurable hA (hd i) L)
  let hs (i : I) := memLp_one_iff_integrable.mpr
    (integrable_graph μ hr (F i).continuous.measurable hA (hd i) L)
  change ‖(hm i).toLp (F i) - (hm j).toLp (F j)‖ =
    ‖(hs i).toLp (fun u => F i (L.graph u)) - (hs j).toLp (fun u => F j (L.graph u))‖
  exact norm_sub_toLp_ambient_eq_source L μ (F i) (F j)
    (F i).continuous.measurable (F j).continuous.measurable (hm i) (hm j) (hs i) (hs j)

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit hf hdecay in
include hJ hr hA hfast in
/-- Actual ambient graph-leaf compactness follows from the derived local
Ascoli/tail argument and the proved exact distance identity. -/
theorem isCompact_closure_ambientLeafFamily (H : Equicontinuous (fun i x => F i x)) :
    IsCompact (closure (Set.range (ambientLeafFamily μ hJ hr hA F hfast))) := by
  let q : ∀ _ : Unit, I → LeafSpace (E := E) μ (J := J) :=
    fun _ => leafFamily μ hJ hr hA F hfast
  have hc := isCompact_closure_leafFamily μ hJ hr hA F hfast H
  have ht : TotallyBounded (q () '' (univ : Set I)) := by
    simpa only [q, image_univ] using hc.totallyBounded.subset subset_closure
  have hout := CompactnessFromComponents.isCompact_closure_image_of_controls
    (univ : Set I) (ambientLeafFamily μ hJ hr hA F hfast) q (fun ε hε => by
      refine ⟨(), ε, hε, ht, ?_⟩
      intro i _ j _ hij
      rwa [dist_ambientLeafFamily_eq_source] )
  simpa only [image_univ] using hout

end Haar

end LeanShared.GraphLeafNorm
