module
public import LeanShared.Geometry.BundleEndomorphismCoordinates
public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Topology.Algebra.Support

/-! Genuine local bundle endomorphisms reconstructed from actual continuous
operator coordinates have continuous total-space action. -/
public noncomputable section
open scoped Topology
namespace LeanShared.LocalBundleEndomorphism
open Set Bundle
variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  (e : Trivialization F (Bundle.TotalSpace.proj (E := E))) [e.IsLinear ℝ]

@[expose] def decode (G : B → F →L[ℝ] F) (b : B) : E b →L[ℝ] E b :=
  (e.symmL ℝ b).comp ((G b).comp (e.continuousLinearMapAt ℝ b))

omit [VectorBundle ℝ F E] in
theorem continuousOn_action (G : B → F →L[ℝ] F) (continuous : Continuous G) :
    ContinuousOn (fun v : TotalSpace F E =>
      (⟨v.proj,decode E e G v.proj v.2⟩ : TotalSpace F E)) e.source := by
  let h : B × F → B × F := fun z => (z.1,G z.1 z.2)
  have hcontinuous : Continuous h := continuous_fst.prodMk
    ((continuous.comp continuous_fst).clm_apply continuous_snd)
  have first := hcontinuous.comp_continuousOn e.continuousOn
  have second := e.continuousOn_symm.comp first (by
    intro v hv
    have base : (e v).1 ∈ e.baseSet := e.mem_target.mp (e.map_source hv)
    exact ⟨base,mem_univ _⟩)
  apply second.congr
  intro v hv
  have hb := e.mem_source.mp hv
  simp only [h,Function.comp_def,e.coe_fst hv]
  simp only [decode,ContinuousLinearMap.comp_apply,e.symmL_apply hb,
    Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hb]
  rw [e.coe_fst hv]
/-- An actual supported scalar cutoff globalizes the local coordinate
operator, with the zero action proved across every chart boundary. -/
theorem continuous_cutoff_action (θ : B → ℝ) (continuousθ : Continuous θ)
    (support : tsupport θ ⊆ e.baseSet)
    (G : B → F →L[ℝ] F) (continuousG : Continuous G) :
    Continuous (fun v : TotalSpace F E =>
      (⟨v.proj,decode E e (fun b => θ b • G b) v.proj v.2⟩ : TotalSpace F E)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  by_cases inside : v.proj ∈ tsupport θ
  · exact ((continuousOn_action E e (fun b => θ b • G b)
      (continuousθ.smul continuousG)) v (e.mem_source.mpr (support inside))).continuousAt
      (e.open_source.mem_nhds (e.mem_source.mpr (support inside)))
  · have zeros : θ =ᶠ[nhds v.proj] 0 := notMem_tsupport_iff_eventuallyEq.mp inside
    have lifted := zeros.comp_tendsto (FiberBundle.continuous_proj F E).continuousAt
    have agrees : (fun w : TotalSpace F E =>
        (⟨w.proj,decode E e (fun b => θ b • G b) w.proj w.2⟩ : TotalSpace F E)) =ᶠ[nhds v]
        (fun w : TotalSpace F E => zeroSection F E w.proj) := by
      filter_upwards [lifted] with w hw
      change θ w.proj=0 at hw
      simp only [decode,ContinuousLinearMap.comp_apply,hw,zero_smul,
        zero_apply,map_zero,zeroSection]
    exact ((Bundle.Trivialization.continuous_zeroSection ℝ).comp
      (FiberBundle.continuous_proj F E)).continuousAt.congr_of_eventuallyEq agrees
end LeanShared.LocalBundleEndomorphism
