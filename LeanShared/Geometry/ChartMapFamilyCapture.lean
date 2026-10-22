module
public import LeanShared.Geometry.ChartMapC1Globalization
public import LeanShared.Analysis.CompactFiberCapture
public import LeanShared.Analysis.CompactSmoothCutoff

/-! One genuine smooth overlap cutoff works for every nearby member of
an actual continuous manifold-map family. Both active-pair capture and
validity of its compact support are derived from compactness. -/
public noncomputable section
open Set Filter IsManifold Metric
open scoped Manifold ContDiff Topology
namespace LeanShared.ChartMapFamilyCapture
variable {P E M:Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  (e f:OpenPartialHomeomorph M E) (θ:M→ℂ)
  (compactθ:HasCompactSupport θ) (supportθ:tsupport θ⊆e.source)
  {K:Set E} (compactK:IsCompact K) (targetK:K⊆f.target)
  (F:P→M→M) (joint:Continuous (fun z:P×M=>F z.1 z.2)) (p:P)

include compactθ supportθ compactK targetK joint in
omit [ChartedSpace E M] in
theorem exists_capture : ∃ρ:E→ℝ,ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
    ∃O:Set P,IsOpen O ∧ p∈O ∧
      (∀a∈O,tsupport ρ⊆ChartMapC1Globalization.domain e f (F a)) ∧
      (∀a∈O,∀x∈tsupport θ,F a x∈f.symm '' K→ρ (e x)=1) := by
  have continuousF:∀a,Continuous (F a) := fun a=>joint.comp (continuous_const.prodMk continuous_id)
  let C:Set M := tsupport θ ∩ (F p) ⁻¹' (f.symm '' K)
  have compactImage:IsCompact (f.symm '' K) :=
    compactK.image_of_continuousOn (f.continuousOn_symm.mono targetK)
  have compactC:IsCompact C := compactθ.inter_right (compactImage.isClosed.preimage (continuousF p))
  let L:Set E := e '' C
  have compactL:IsCompact L := compactC.image_of_continuousOn
    (e.continuousOn.mono (fun _ hx=>supportθ hx.1))
  let W:=ChartMapC1Globalization.domain e f (F p)
  have openW:IsOpen W :=
    ((continuousF p).comp_continuousOn e.continuousOn_symm).isOpen_inter_preimage e.open_target f.open_source
  have inW:L⊆W := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨e.map_source (supportθ hx.1),?_⟩
    change F p (e.symm (e x))∈f.source
    rw [e.left_inv (supportθ hx.1)]
    obtain ⟨z,hz,eqn⟩:=hx.2
    rw [←eqn]
    exact f.map_target (targetK hz)
  obtain ⟨δ,hδ,safe⟩:=compactL.exists_cthickening_subset_open openW inW
  let L₁:=cthickening (δ/2) L
  have compactL₁:IsCompact L₁:=compactL.cthickening
  have safeL₁:L₁⊆W := (cthickening_mono (by linarith : δ/2≤δ) L).trans safe
  obtain ⟨ρ,hρ,cρ,sρ,_,oneρ⟩:=CompactSmoothCutoff.exists_cutoff compactL₁ openW safeL₁
  let capture:Set M := e.source ∩ e ⁻¹' thickening (δ/2) L
  have openCapture:IsOpen capture := e.continuousOn.isOpen_inter_preimage e.open_source isOpen_thickening
  let relation:Set (P×M):={z|F z.1 z.2∈f.symm '' K}
  have closedRelation:IsClosed relation := compactImage.isClosed.preimage joint
  have refCapture:CylinderPrincipalCoefficient.fiber (tsupport θ) relation p⊆capture := by
    intro x hx
    exact ⟨supportθ hx.1,self_subset_thickening (by linarith) L ⟨x,hx,rfl⟩⟩
  obtain ⟨O₁,hO₁,hp₁,captured⟩:=CompactFiberCapture.exists_open_capture
    (tsupport θ) compactθ relation closedRelation p capture openCapture refCapture
  let domain:Set (P×E):=univ ×ˢ e.target
  have openDomain:IsOpen domain:=isOpen_univ.prod e.open_target
  have continuousCoordinate:ContinuousOn (fun z:P×E=>F z.1 (e.symm z.2)) domain :=
    joint.comp_continuousOn (continuousOn_fst.prodMk
      (e.continuousOn_symm.comp continuousOn_snd (fun _ hz=>hz.2)))
  let valid:Set (P×E):=domain ∩ (fun z:P×E=>F z.1 (e.symm z.2)) ⁻¹' f.source
  have openValid:IsOpen valid:=continuousCoordinate.isOpen_inter_preimage openDomain f.open_source
  have contains:({p}:Set P)×ˢtsupport ρ⊆valid := by
    rintro ⟨a,y⟩ ⟨ha,hy⟩
    rcases mem_singleton_iff.mp ha with rfl
    exact ⟨⟨mem_univ _,(sρ hy).1⟩,(sρ hy).2⟩
  obtain ⟨O₂,Y,hO₂,_,hp₂,hY,tube⟩:=generalized_tube_lemma isCompact_singleton cρ openValid contains
  refine ⟨ρ,hρ,cρ,O₁∩O₂,hO₁.inter hO₂,⟨hp₁,singleton_subset_iff.mp hp₂⟩,?_,?_⟩
  · intro a ha y hy
    have h:=tube (show (a,y)∈O₂×ˢY from ⟨ha.2,hY hy⟩)
    exact ⟨h.1.2,h.2⟩
  · intro a ha x hx hFx
    have hit:=captured a ha.1 ⟨hx,hFx⟩
    exact oneρ (thickening_subset_cthickening (δ/2) L hit.2)
end LeanShared.ChartMapFamilyCapture
