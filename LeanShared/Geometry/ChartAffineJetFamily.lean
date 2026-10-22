module
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-! Actual local manifold maps are synthesized from an input chart point,
output chart point, and a linear coordinate derivative. Their joint
regularity is proved only on the genuine open chart-validity domain. -/
@[expose] public noncomputable section
open Set IsManifold Filter
open scoped Manifold ContDiff Topology
namespace LeanShared.ChartAffineJetFamily
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

abbrev Jet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E × E × (E →L[ℝ] E)

def argument (c : OpenPartialHomeomorph M E) (z : Jet E × M) : E :=
  z.1.2.1 + z.1.2.2 (c z.2 - z.1.1)

def synthesis (c d : OpenPartialHomeomorph M E) (z : Jet E × M) : M := d.symm (argument c z)

def domain (c d : OpenPartialHomeomorph M E) : Set (Jet E × M) :=
  {z | z.2 ∈ c.source ∧ argument c z ∈ d.target}

theorem argument_regular (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) :
    ContMDiffOn ((𝓘(ℝ,Jet E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
      (argument c) {z : Jet E × M | z.2 ∈ c.source} := by
  have first : ContMDiff ((𝓘(ℝ,Jet E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
      (fun z : Jet E × M => z.1.1) :=
    (contDiff_fst : ContDiff ℝ ∞ (fun q : Jet E => q.1)).contMDiff.comp contMDiff_fst
  have second : ContMDiff ((𝓘(ℝ,Jet E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
      (fun z : Jet E × M => z.1.2.1) :=
    (contDiff_snd.fst : ContDiff ℝ ∞ (fun q : Jet E => q.2.1)).contMDiff.comp contMDiff_fst
  have linear : ContMDiff ((𝓘(ℝ,Jet E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun z : Jet E × M => z.1.2.2) :=
    (contDiff_snd.snd : ContDiff ℝ ∞ (fun q : Jet E => q.2.2)).contMDiff.comp contMDiff_fst
  intro z hz
  have chart : ContMDiffAt ((𝓘(ℝ,Jet E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞
      (fun z : Jet E × M => c z.2) z :=
    (contMDiffAt_of_mem_maximalAtlas hc hz).comp z contMDiffAt_snd
  exact (second.contMDiffAt.add (linear.contMDiffAt.clm_apply
    (chart.sub first.contMDiffAt))).contMDiffWithinAt

theorem domain_open (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) : IsOpen (domain c d) :=
  (argument_regular c hc).continuousOn.isOpen_inter_preimage
    (c.open_source.preimage continuous_snd) d.open_target

theorem synthesis_regular (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) :
    ContMDiffOn ((𝓘(ℝ,Jet E)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) ∞ (synthesis c d) (domain c d) := by
  intro z hz
  have arg := ((argument_regular c hc) z hz.1).contMDiffAt
    ((c.open_source.preimage continuous_snd).mem_nhds hz.1)
  exact ((contMDiffAt_symm_of_mem_maximalAtlas hd hz.2).comp z arg).contMDiffWithinAt

omit [ChartedSpace E M] in
theorem synthesis_at_center (c d : OpenPartialHomeomorph M E) (f : M → M)
    (x : M) (L : E →L[ℝ] E) (target : f x ∈ d.source) :
    synthesis c d ((c x,d (f x),L),x) = f x := by
  rw [synthesis,argument,sub_self,map_zero,add_zero,d.left_inv target]

omit [ChartedSpace E M] in
theorem coordinate_germ (c d : OpenPartialHomeomorph M E) (q : Jet E)
    (source : q.1 ∈ c.target) (target : q.2.1 ∈ d.target) :
    (fun z => d (synthesis c d (q,c.symm z))) =ᶠ[𝓝 q.1]
      (fun z => q.2.1 + q.2.2 (z-q.1)) := by
  have affine : Continuous (fun z : E => q.2.1 + q.2.2 (z-q.1)) :=
    continuous_const.add (q.2.2.continuous.comp (continuous_id.sub continuous_const))
  have image : ∀ᶠ z : E in 𝓝 q.1, q.2.1 + q.2.2 (z-q.1) ∈ d.target :=
    affine.continuousAt.preimage_mem_nhds (d.open_target.mem_nhds (by
      simpa only [sub_self,map_zero,add_zero] using target))
  filter_upwards [c.open_target.mem_nhds source,image] with z sourceZ targetZ
  dsimp only [synthesis,argument]
  rw [c.right_inv sourceZ,d.right_inv targetZ]

omit [ChartedSpace E M] in
theorem coordinate_fderiv (c d : OpenPartialHomeomorph M E) (q : Jet E)
    (source : q.1 ∈ c.target) (target : q.2.1 ∈ d.target) :
    fderiv ℝ (fun z => d (synthesis c d (q,c.symm z))) q.1 = q.2.2 := by
  rw [(coordinate_germ c d q source target).fderiv_eq]
  have affine := ((q.2.2.hasFDerivAt).comp q.1
    ((hasFDerivAt_id q.1).sub_const q.1)).const_add q.2.1
  simpa only [ContinuousLinearMap.comp_id,Function.comp_apply,id_eq] using affine.fderiv

end LeanShared.ChartAffineJetFamily
