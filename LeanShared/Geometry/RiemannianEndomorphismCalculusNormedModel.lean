module
public import LeanShared.Geometry.BundleOrthonormalCoordinates
public import LeanShared.Geometry.ContinuousRiemannianFramesNormedModel
public import LeanShared.Analysis.FiniteHilbertSpectralRetraction
public import LeanShared.Analysis.FiniteHilbertProjectionNaturality

public noncomputable section
namespace LeanShared.RiemannianEndomorphismCalculusNormedModel
open Set Bundle
open scoped Topology
variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [∀ b, FiniteDimensional ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]

@[expose] def localBasis (D : Set B) (e : Trivialization F (Bundle.TotalSpace.proj (E := E)))
    [e.IsLinear ℝ] (b : ↥(D ∩ e.baseSet)) :
    OrthonormalBasis (Fin (Module.finrank ℝ (ContinuousRiemannianFramesNormedModel.Model (F := F)))) ℝ (E b.val) :=
  ContinuousRiemannianFramesNormedModel.basis E e ⟨b.val,b.property.2⟩

theorem continuous_local_sections (D : Set B)
    (e : Trivialization F (Bundle.TotalSpace.proj (E := E))) [e.IsLinear ℝ]
    (i : Fin (Module.finrank ℝ (ContinuousRiemannianFramesNormedModel.Model (F := F)))) : Continuous
      (fun b : ↥(D ∩ e.baseSet) => (⟨b.val,localBasis E D e b i⟩ : TotalSpace F E)) := by
  exact (ContinuousRiemannianFramesNormedModel.continuous_basis_section E e i).comp
    (continuous_subtype_val.subtype_mk (fun b => b.property.2))

private theorem continuousOn_of_local (D : Set B) (Q : ∀ b, E b →L[ℝ] E b)
    (patches : ∀ x : B, Continuous (BundleOrthonormalCoordinates.coordinates E
      (D ∩ (trivializationAt F E x).baseSet) (localBasis E D (trivializationAt F E x)) Q)) :
    ContinuousOn (fun v : TotalSpace F E => (⟨v.proj,Q v.proj v.2⟩ : TotalSpace F E))
      {v | v.proj ∈ D} := by
  intro v hv
  let e := trivializationAt F E v.proj
  have onPatch := BundleOrthonormalCoordinates.continuous_action_of_coordinates E
    (D∩e.baseSet) (localBasis E D e) (continuous_local_sections E D e) Q (patches v.proj)
  have inside : v ∈ {v : TotalSpace F E | v.proj ∈ D∩e.baseSet} :=
    ⟨hv,FiberBundle.mem_baseSet_trivializationAt' v.proj⟩
  have ht : {w : TotalSpace F E | w.proj ∈ e.baseSet} ∈ 𝓝 v :=
    ((FiberBundle.continuous_proj F E).isOpen_preimage _ e.open_baseSet).mem_nhds inside.2
  exact (continuousWithinAt_inter ht).mp (onPatch v inside)

theorem continuousOn_star (D : Set B) (P : ∀ b, E b →L[ℝ] E b)
    (action : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj,P v.proj v.2⟩ : TotalSpace F E)) {v | v.proj ∈ D}) :
    ContinuousOn (fun v : TotalSpace F E => (⟨v.proj,star (P v.proj) v.2⟩ : TotalSpace F E))
      {v | v.proj ∈ D} := by
  apply continuousOn_of_local (F := F) E D (fun b => star (P b))
  intro x
  let e := trivializationAt F E x
  let basis := localBasis E D e
  have hc := BundleOrthonormalCoordinates.continuous_coordinates E (D∩e.baseSet) basis
    (continuous_local_sections E D e) P (action.mono (fun _ h => h.1))
  apply (ContinuousLinearMap.adjoint.continuous.comp hc).congr
  intro b
  exact (map_star (basis b).repr.conjStarAlgEquiv (P b.val)).symm
theorem continuousOn_norm (D : Set B) (P : ∀ b, E b →L[ℝ] E b)
    (action : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj,P v.proj v.2⟩ : TotalSpace F E)) {v | v.proj ∈ D}) :
    ContinuousOn (fun b => ‖P b‖) D := by
  intro x hx
  let e := trivializationAt F E x
  let basis := localBasis E D e
  have hc := BundleOrthonormalCoordinates.continuous_coordinates E (D∩e.baseSet) basis
    (continuous_local_sections E D e) P (action.mono (fun _ h => h.1))
  have hn : Continuous (fun b : ↥(D∩e.baseSet) => ‖P b.val‖) := hc.norm.congr
    (fun b => FiniteHilbertSpectralRetraction.norm_conjugate (basis b).repr (P b.val))
  have onPatch : ContinuousOn (fun b : B => ‖P b‖) (D∩e.baseSet) :=
    continuousOn_iff_continuous_domRestrict.mpr hn
  exact (continuousWithinAt_inter (e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x))).mp
      (onPatch x ⟨hx,FiberBundle.mem_baseSet_trivializationAt' x⟩)

theorem continuousOn_symmetrize (D : Set B) (P : ∀ b, E b →L[ℝ] E b)
    (action : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj,P v.proj v.2⟩ : TotalSpace F E)) {v | v.proj ∈ D}) :
    ContinuousOn (fun v : TotalSpace F E =>
      (⟨v.proj,((1/2:ℝ) • (P v.proj+star (P v.proj))) v.2⟩ : TotalSpace F E))
      {v | v.proj ∈ D} := by
  apply continuousOn_of_local (F := F) E D (fun b => (1/2:ℝ) • (P b+star (P b)))
  intro x
  let e := trivializationAt F E x
  let basis := localBasis E D e
  have hc := BundleOrthonormalCoordinates.continuous_coordinates E (D∩e.baseSet) basis
    (continuous_local_sections E D e) P (action.mono (fun _ h => h.1))
  have hs := ContinuousLinearMap.adjoint.continuous.comp hc
  have actual := (continuous_const : Continuous (fun _ : ↥(D∩e.baseSet) => (1/2:ℝ))).smul (hc.add hs)
  apply actual.congr
  intro b
  simp only [BundleOrthonormalCoordinates.coordinates,map_smul,map_add,map_star]
  rfl

theorem continuousOn_retract (D : Set B) (P : ∀ b, E b →L[ℝ] E b)
    (action : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj,P v.proj v.2⟩ : TotalSpace F E)) {v | v.proj ∈ D})
    (self : ∀ b ∈ D, IsSelfAdjoint (P b)) (small : ∀ b ∈ D, ‖P b^2-P b‖<(3/16:ℝ)) :
    ContinuousOn (fun v : TotalSpace F E =>
      (⟨v.proj,FiniteHilbertSpectralRetraction.retract (P v.proj) v.2⟩ : TotalSpace F E))
      {v | v.proj ∈ D} := by
  apply continuousOn_of_local (F := F) E D (fun b => FiniteHilbertSpectralRetraction.retract (P b))
  intro x
  let e := trivializationAt F E x
  let basis := localBasis E D e
  let A := BundleOrthonormalCoordinates.coordinates E (D∩e.baseSet) basis P
  have hc := BundleOrthonormalCoordinates.continuous_coordinates E (D∩e.baseSet) basis
    (continuous_local_sections E D e) P (action.mono (fun _ h => h.1))
  have conditions (b : ↥(D∩e.baseSet)) : IsSelfAdjoint (A b) ∧ ‖A b^2-A b‖<(3/16:ℝ) := by
    let a := (basis b).repr.conjStarAlgEquiv
    have hself : IsSelfAdjoint (a (P b.val)) := by
      change star (a (P b.val))=a (P b.val)
      rw [← map_star a,(self b.val b.property.1).star_eq]
    refine ⟨hself,?_⟩
    change ‖a (P b.val)^2-a (P b.val)‖<(3/16:ℝ)
    rw [← map_pow,← map_sub,FiniteHilbertSpectralRetraction.norm_conjugate]
    exact small b.val b.property.1
  have onAll : ContinuousOn (fun b : ↥(D∩e.baseSet) => FiniteHilbertSpectralRetraction.retract (A b)) univ :=
    FiniteHilbertSpectralRetraction.continuousOn.comp hc.continuousOn (fun b _ => conditions b)
  have actual := continuousOn_univ.mp onAll
  apply actual.congr
  intro b
  exact FiniteHilbertSpectralRetraction.conjugate (basis b).repr (P b.val) (self b.val b.property.1)

theorem continuousOn_defect_norm (D : Set B) (P : ∀ b, E b →L[ℝ] E b)
    (action : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj,P v.proj v.2⟩ : TotalSpace F E)) {v | v.proj ∈ D}) :
    ContinuousOn (fun b => ‖P b^2-P b‖) D := by
  intro x hx
  let e := trivializationAt F E x
  let basis := localBasis E D e
  have hc := BundleOrthonormalCoordinates.continuous_coordinates E (D∩e.baseSet) basis
    (continuous_local_sections E D e) P (action.mono (fun _ h => h.1))
  have hn : Continuous (fun b : ↥(D∩e.baseSet) => ‖P b.val^2-P b.val‖) := by
    apply ((hc.pow 2).sub hc).norm.congr
    intro b
    simp only [Pi.pow_apply,Pi.sub_apply,BundleOrthonormalCoordinates.coordinates]
    rw [← map_pow,← map_sub,FiniteHilbertSpectralRetraction.norm_conjugate]
  have onPatch : ContinuousOn (fun b : B => ‖P b^2-P b‖) (D∩e.baseSet) :=
    continuousOn_iff_continuous_domRestrict.mpr hn
  exact (continuousWithinAt_inter (e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x))).mp
      (onPatch x ⟨hx,FiberBundle.mem_baseSet_trivializationAt' x⟩)

theorem continuousOn_orthogonalize (D : Set B) (P : ∀ b, E b →L[ℝ] E b)
    (action : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj,P v.proj v.2⟩ : TotalSpace F E)) {v | v.proj ∈ D})
    (idem : ∀ b ∈ D, IsIdempotentElem (P b)) :
    ContinuousOn (fun v : TotalSpace F E =>
      (⟨v.proj,ContinuousIdempotentOrthogonalization.orthogonalize (P v.proj) v.2⟩ : TotalSpace F E))
      {v | v.proj ∈ D} := by
  apply continuousOn_of_local (F := F) E D
    (fun b => ContinuousIdempotentOrthogonalization.orthogonalize (P b))
  intro x
  let e := trivializationAt F E x
  let basis := localBasis E D e
  let A := BundleOrthonormalCoordinates.coordinates E (D∩e.baseSet) basis P
  have hc := BundleOrthonormalCoordinates.continuous_coordinates E (D∩e.baseSet) basis
    (continuous_local_sections E D e) P (action.mono (fun _ h => h.1))
  have idempotent (b : ↥(D∩e.baseSet)) : IsIdempotentElem (A b) := by
    change (basis b).repr.conjStarAlgEquiv (P b.val) *
      (basis b).repr.conjStarAlgEquiv (P b.val) = (basis b).repr.conjStarAlgEquiv (P b.val)
    rw [← map_mul,(idem b.val b.property.1).eq]
  have onAll := ContinuousIdempotentOrthogonalization.continuousOn univ A hc.continuousOn
    (fun b _ => idempotent b)
  have actual := continuousOn_univ.mp onAll
  apply actual.congr
  intro b
  exact (FiniteHilbertProjectionNaturality.orthogonalize (basis b).repr (P b.val)
    (idem b.val b.property.1)).symm

theorem continuousOn_oneSub (D : Set B) (P : ∀ b, E b →L[ℝ] E b)
    (action : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj,P v.proj v.2⟩ : TotalSpace F E)) {v | v.proj ∈ D}) :
    ContinuousOn (fun v : TotalSpace F E => (⟨v.proj,(1-P v.proj) v.2⟩ : TotalSpace F E))
      {v | v.proj ∈ D} := by
  apply continuousOn_of_local (F := F) E D (fun b => 1-P b)
  intro x
  let e := trivializationAt F E x
  let basis := localBasis E D e
  have hc := BundleOrthonormalCoordinates.continuous_coordinates E (D∩e.baseSet) basis
    (continuous_local_sections E D e) P (action.mono (fun _ h => h.1))
  apply ((continuous_const : Continuous (fun _ : ↥(D∩e.baseSet) =>
    (1 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (ContinuousRiemannianFramesNormedModel.Model (F := F)))) →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (ContinuousRiemannianFramesNormedModel.Model (F := F))))))).sub hc).congr
  intro b
  simp only [Pi.sub_apply,BundleOrthonormalCoordinates.coordinates,map_sub,map_one]
  rfl

theorem continuousOn_sub (D : Set B) (P Q : ∀ b, E b →L[ℝ] E b)
    (actionP : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj,P v.proj v.2⟩ : TotalSpace F E)) {v | v.proj ∈ D})
    (actionQ : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj,Q v.proj v.2⟩ : TotalSpace F E)) {v | v.proj ∈ D}) :
    ContinuousOn (fun v : TotalSpace F E => (⟨v.proj,(P v.proj-Q v.proj) v.2⟩ : TotalSpace F E))
      {v | v.proj ∈ D} := by
  apply continuousOn_of_local (F := F) E D (fun b => P b-Q b)
  intro x
  let e := trivializationAt F E x
  let basis := localBasis E D e
  have hcP := BundleOrthonormalCoordinates.continuous_coordinates E (D∩e.baseSet) basis
    (continuous_local_sections E D e) P (actionP.mono (fun _ h => h.1))
  have hcQ := BundleOrthonormalCoordinates.continuous_coordinates E (D∩e.baseSet) basis
    (continuous_local_sections E D e) Q (actionQ.mono (fun _ h => h.1))
  apply (hcP.sub hcQ).congr
  intro b
  simp only [Pi.sub_apply,BundleOrthonormalCoordinates.coordinates,map_sub]
  rfl

theorem isOpen_isUnit (D : Set B) (openD : IsOpen D) (P : ∀ b, E b →L[ℝ] E b)
    (action : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj,P v.proj v.2⟩ : TotalSpace F E)) {v | v.proj ∈ D}) :
    IsOpen {b | b∈D ∧ IsUnit (P b)} := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  let e := trivializationAt F E x
  let basis := localBasis E D e
  let A := BundleOrthonormalCoordinates.coordinates E (D∩e.baseSet) basis P
  have hc := BundleOrthonormalCoordinates.continuous_coordinates E (D∩e.baseSet) basis
    (continuous_local_sections E D e) P (action.mono (fun _ h => h.1))
  let V := {b : ↥(D∩e.baseSet) | IsUnit (A b)}
  have openV : IsOpen V := hc.isOpen_preimage _ Units.isOpen
  refine ⟨Subtype.val '' V,?_,(openD.inter e.open_baseSet).isOpenMap_subtype_val V openV,?_⟩
  · rintro b ⟨c,hc,rfl⟩
    refine ⟨c.property.1,?_⟩
    have mapped := hc.map (basis c).repr.conjStarAlgEquiv.symm.toMonoidHom
    change IsUnit ((basis c).repr.conjStarAlgEquiv.symm ((basis c).repr.conjStarAlgEquiv (P c.val))) at mapped
    simpa only [StarAlgEquiv.symm_apply_apply] using mapped
  · let c : ↥(D∩e.baseSet) := ⟨x,hx.1,FiberBundle.mem_baseSet_trivializationAt' x⟩
    exact ⟨c,hx.2.map (basis c).repr.conjStarAlgEquiv.toMonoidHom,rfl⟩

theorem continuousOn_reconstruct (D : Set B) (R S : ∀ b, E b →L[ℝ] E b)
    (actionR : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj,R v.proj v.2⟩ : TotalSpace F E)) {v | v.proj ∈ D})
    (actionS : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj,S v.proj v.2⟩ : TotalSpace F E)) {v | v.proj ∈ D})
    (unit : ∀ b∈D, IsUnit (R b-S b)) :
    ContinuousOn (fun v : TotalSpace F E =>
      (⟨v.proj,ComplementaryProjectionReconstruction.reconstruct (R v.proj) (S v.proj) v.2⟩ : TotalSpace F E))
      {v | v.proj ∈ D} := by
  apply continuousOn_of_local (F := F) E D
    (fun b => ComplementaryProjectionReconstruction.reconstruct (R b) (S b))
  intro x
  let e := trivializationAt F E x
  let basis := localBasis E D e
  let A := BundleOrthonormalCoordinates.coordinates E (D∩e.baseSet) basis R
  let C := BundleOrthonormalCoordinates.coordinates E (D∩e.baseSet) basis S
  have hcR := BundleOrthonormalCoordinates.continuous_coordinates E (D∩e.baseSet) basis
    (continuous_local_sections E D e) R (actionR.mono (fun _ h => h.1))
  have hcS := BundleOrthonormalCoordinates.continuous_coordinates E (D∩e.baseSet) basis
    (continuous_local_sections E D e) S (actionS.mono (fun _ h => h.1))
  have inverse : Continuous (fun b => Ring.inverse (A b-C b)) := by
    apply continuous_iff_continuousAt.mpr
    intro b
    have mapped := (unit b.val b.property.1).map (basis b).repr.conjStarAlgEquiv.toMonoidHom
    have hm : IsUnit (A b-C b) := by
      change IsUnit ((basis b).repr.conjStarAlgEquiv (R b.val-S b.val)) at mapped
      rw [map_sub] at mapped
      exact mapped
    obtain ⟨u,hu⟩ := hm
    have hi : ContinuousAt Ring.inverse (A b-C b) := by
      rw [←hu]
      exact NormedRing.inverse_continuousAt u
    exact hi.comp (f := fun y : ↥(D∩e.baseSet) => A y-C y) (hcR.sub hcS).continuousAt
  apply (hcR.mul inverse).congr
  intro b
  exact (FiniteHilbertProjectionNaturality.reconstruct (basis b).repr (R b.val) (S b.val)
    (unit b.val b.property.1)).symm

end LeanShared.RiemannianEndomorphismCalculusNormedModel
