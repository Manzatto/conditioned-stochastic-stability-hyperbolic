module
public import LeanShared.Geometry.TangentEndomorphismExtension
public import LeanShared.Geometry.RiemannianEndomorphismCalculusNormedModel

public noncomputable section
namespace LeanShared.TangentProjectionExtensionNormedModel
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]

private theorem orthogonal (K : Set M) (compact : IsCompact K)
    (P : ∀ x : M, TangentSpace (𝓘(ℝ,E)) x →L[ℝ] TangentSpace (𝓘(ℝ,E)) x)
    (action : ContinuousOn
      (fun v : TotalSpace E (TangentSpace (𝓘(ℝ,E))) =>
        (⟨v.proj,P v.proj v.2⟩ : TotalSpace E (TangentSpace (𝓘(ℝ,E))))) {v | v.proj ∈ K})
    (self : ∀ x∈K, IsSelfAdjoint (P x)) (idem : ∀ x∈K, IsIdempotentElem (P x)) :
    ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧
      ∃ Q : ∀ x : M, TangentSpace (𝓘(ℝ,E)) x →L[ℝ] TangentSpace (𝓘(ℝ,E)) x,
      ContinuousOn (fun v : TotalSpace E (TangentSpace (𝓘(ℝ,E))) =>
        (⟨v.proj,Q v.proj v.2⟩ : TotalSpace E (TangentSpace (𝓘(ℝ,E))))) {v | v.proj ∈ U} ∧
      (∀ x∈K,Q x=P x) ∧ (∀ x,IsSelfAdjoint (Q x)) ∧ (∀ x∈U,IsIdempotentElem (Q x)) := by
  obtain ⟨A,continuousA,agreesA⟩ := TangentEndomorphismExtension.exists_extension K compact P action
  let S := fun x => (1/2:ℝ) • (A x+star (A x))
  have actionA : ContinuousOn (fun v : TotalSpace E (TangentSpace (𝓘(ℝ,E))) =>
      (⟨v.proj,A v.proj v.2⟩ : TotalSpace E (TangentSpace (𝓘(ℝ,E))))) {v | v.proj ∈ (univ : Set M)} :=
    continuousA.continuousOn
  have actionS := RiemannianEndomorphismCalculusNormedModel.continuousOn_symmetrize
    (TangentSpace (𝓘(ℝ,E))) univ A actionA
  have selfS (x : M) : IsSelfAdjoint (S x) := by
    change star ((1/2:ℝ) • (A x+star (A x)))=(1/2:ℝ) • (A x+star (A x))
    simp only [star_smul,star_add,star_star,star_trivial]
    congr 1
    exact add_comm _ _
  have agreesS (x : M) (hx : x∈K) : S x=P x := by
    change (1/2:ℝ) • (A x+star (A x))=P x
    rw [agreesA x hx,(self x hx).star_eq,←two_smul ℝ (P x),smul_smul]
    norm_num
  have continuousDefect : Continuous (fun x => ‖S x^2-S x‖) :=
    continuousOn_univ.mp (RiemannianEndomorphismCalculusNormedModel.continuousOn_defect_norm
      (TangentSpace (𝓘(ℝ,E))) univ S actionS)
  let U := {x | ‖S x^2-S x‖<(3/16:ℝ)}
  have openU : IsOpen U := isOpen_lt continuousDefect continuous_const
  have inside : K⊆U := by
    intro x hx
    change ‖S x^2-S x‖<(3/16:ℝ)
    rw [agreesS x hx,pow_two,(idem x hx).eq,sub_self]
    have zero : ‖(0 : TangentSpace (𝓘(ℝ,E)) x →L[ℝ] TangentSpace (𝓘(ℝ,E)) x)‖=0 := ContinuousLinearMap.opNorm_zero
    rw [zero]
    norm_num
  refine ⟨U,openU,inside,fun x => FiniteHilbertSpectralRetraction.retract (S x),?_,?_,?_,?_⟩
  · exact RiemannianEndomorphismCalculusNormedModel.continuousOn_retract
      (TangentSpace (𝓘(ℝ,E))) U S (actionS.mono (fun _ _ => mem_univ _))
      (fun x _ => selfS x) (fun _ hx => hx)
  · intro x hx
    change FiniteHilbertSpectralRetraction.retract (S x)=P x
    rw [agreesS x hx]
    exact FiniteHilbertSpectralRetraction.fixes (P x) (self x hx) (idem x hx)
  · intro x
    exact FiniteHilbertSpectralRetraction.selfAdjoint (S x)
  · intro x hx
    exact FiniteHilbertSpectralRetraction.idempotent (S x) (selfS x) hx

theorem exists_extension (K : Set M) (compact : IsCompact K)
    (P : ∀ x : M, TangentSpace (𝓘(ℝ,E)) x →L[ℝ] TangentSpace (𝓘(ℝ,E)) x)
    (action : ContinuousOn
      (fun v : TotalSpace E (TangentSpace (𝓘(ℝ,E))) =>
        (⟨v.proj,P v.proj v.2⟩ : TotalSpace E (TangentSpace (𝓘(ℝ,E))))) {v | v.proj ∈ K})
    (idem : ∀ x∈K, IsIdempotentElem (P x)) :
    ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧
      ∃ Q : ∀ x : M, TangentSpace (𝓘(ℝ,E)) x →L[ℝ] TangentSpace (𝓘(ℝ,E)) x,
      ContinuousOn (fun v : TotalSpace E (TangentSpace (𝓘(ℝ,E))) =>
        (⟨v.proj,Q v.proj v.2⟩ : TotalSpace E (TangentSpace (𝓘(ℝ,E))))) {v | v.proj ∈ U} ∧
      (∀ x∈K,Q x=P x) ∧ (∀ x∈U,IsIdempotentElem (Q x)) := by
  let R := fun x => ContinuousIdempotentOrthogonalization.orthogonalize (P x)
  let S := fun x => ContinuousIdempotentOrthogonalization.orthogonalize (1-P x)
  have oneSubIdem (x : M) (hx : x∈K) : IsIdempotentElem (1-P x) := by
    change (1-P x)*(1-P x)=1-P x
    noncomm_ring [(idem x hx).eq]
  have rangeOneSub (x : M) (hx : x∈K) : (1-P x).range=(P x).ker := by
    ext v
    constructor
    · rintro ⟨w,rfl⟩
      change P x (w-P x w)=0
      rw [map_sub]
      rw [show P x (P x w)=P x w from congrArg
        (fun A : TangentSpace (𝓘(ℝ,E)) x →L[ℝ] TangentSpace (𝓘(ℝ,E)) x => A w) (idem x hx).eq,sub_self]
    · intro hv
      refine ⟨v,?_⟩
      change v-P x v=v
      rw [show P x v=0 from hv,sub_zero]
  have R_core (x : M) (hx : x∈K) : R x=(P x).range.starProjection :=
    ContinuousIdempotentOrthogonalization.eq_projection (P x) (idem x hx)
  have S_core (x : M) (hx : x∈K) : S x=(P x).ker.starProjection := by
    change ContinuousIdempotentOrthogonalization.orthogonalize (1-P x)=_
    rw [ContinuousIdempotentOrthogonalization.eq_projection (1-P x) (oneSubIdem x hx)]
    apply (ContinuousLinearMap.IsStarProjection.ext_iff isStarProjection_starProjection
      isStarProjection_starProjection).mpr
    simpa only [Submodule.range_starProjection] using rangeOneSub x hx
  have contR := RiemannianEndomorphismCalculusNormedModel.continuousOn_orthogonalize
    (TangentSpace (𝓘(ℝ,E))) K P action idem
  have contS := RiemannianEndomorphismCalculusNormedModel.continuousOn_orthogonalize
    (TangentSpace (𝓘(ℝ,E))) K (fun x => 1-P x)
    (RiemannianEndomorphismCalculusNormedModel.continuousOn_oneSub (TangentSpace (𝓘(ℝ,E))) K P action) oneSubIdem
  obtain ⟨UR,openR,insideR,Rext,continuousR,agreesR,_selfR,idemR⟩ :=
    orthogonal K compact R contR
      (fun x hx => by rw [R_core x hx]; exact isSelfAdjoint_starProjection _)
      (fun x hx => by rw [R_core x hx]; exact (P x).range.isIdempotentElem_starProjection)
  obtain ⟨US,openS,insideS,Sext,continuousS,agreesS,_selfS,idemS⟩ :=
    orthogonal K compact S contS
      (fun x hx => by rw [S_core x hx]; exact isSelfAdjoint_starProjection _)
      (fun x hx => by rw [S_core x hx]; exact (P x).ker.isIdempotentElem_starProjection)
  let U := {x | x∈UR∩US ∧ IsUnit (Rext x-Sext x)}
  have difference := RiemannianEndomorphismCalculusNormedModel.continuousOn_sub
    (TangentSpace (𝓘(ℝ,E))) (UR∩US) Rext Sext
    (continuousR.mono (fun _ hx => hx.1)) (continuousS.mono (fun _ hx => hx.2))
  have openU : IsOpen U := RiemannianEndomorphismCalculusNormedModel.isOpen_isUnit
    (TangentSpace (𝓘(ℝ,E))) (UR∩US) (openR.inter openS) (fun x => Rext x-Sext x) difference
  have inside : K⊆U := by
    intro x hx
    refine ⟨⟨insideR hx,insideS hx⟩,?_⟩
    rw [agreesR x hx,agreesS x hx,R_core x hx,S_core x hx]
    exact ComplementaryProjectionReconstruction.range_kernel_difference_isUnit (P x) (idem x hx)
  refine ⟨U,openU,inside,fun x => ComplementaryProjectionReconstruction.reconstruct (Rext x) (Sext x),?_,?_,?_⟩
  · exact RiemannianEndomorphismCalculusNormedModel.continuousOn_reconstruct
      (TangentSpace (𝓘(ℝ,E))) U Rext Sext
      (continuousR.mono (fun _ hx => hx.1.1)) (continuousS.mono (fun _ hx => hx.1.2)) (fun _ hx => hx.2)
  · intro x hx
    change ComplementaryProjectionReconstruction.reconstruct (Rext x) (Sext x)=P x
    rw [agreesR x hx,agreesS x hx,R_core x hx,S_core x hx]
    exact ComplementaryProjectionReconstruction.fixes (P x) (idem x hx)
  · intro x hx
    exact (ComplementaryProjectionReconstruction.properties (Rext x) (Sext x)
      (idemR x hx.1.1) (idemS x hx.1.2) hx.2).1

end LeanShared.TangentProjectionExtensionNormedModel
