module
public import LeanShared.Geometry.EuclideanSmoothHolderCore
public import LeanShared.Analysis.HolderWeightComposition

/-! Genuine linear coordinate changes preserve the closed little Holder
cores. The bounded map is constructed from Lipschitz precomposition, and
its action on every completed vector is the literal physical composition. -/
@[expose] public noncomputable section
open Set
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.LittleHolderLinearPrecomposition
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {V : Set E} {W : Set F} (e : E ≃L[ℝ] F) (cover : e '' V ⊆ W)

def smoothCore : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ]
    SmoothSupportedManifoldCore.core (E := F) W where
  toFun c := ⟨fun x => c.val (e.symm x),
    c.property.1.comp e.symm.contDiff.contMDiff,by
      change tsupport (c.val ∘ e.symm.toHomeomorph) ⊆ W
      rw [tsupport_comp_eq_preimage]
      intro x hx
      exact cover ⟨e.symm x,c.property.2 hx,e.apply_symm_apply x⟩⟩
  map_add' c d := by apply Subtype.ext; rfl
  map_smul' z c := by apply Subtype.ext; rfl

variable {b : ℝ} (hb : 0 < b) (hb1 : b < 1)

def graphMap : BoundedHolderSpace.graph E b →L[ℂ] BoundedHolderSpace.graph F b :=
  HolderWeightComposition.operator hb.le (1 : F →ᵇ ℂ) (Cψ := 0) (by norm_num)
    (by intro x y; simp) e.symm e.symm.toContinuousLinearMap.lipschitzWith

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem graphMap_physical (v : BoundedHolderSpace.graph E b) (x : F) :
    BoundedHolderSpace.physical F b (graphMap e hb v) x =
      BoundedHolderSpace.physical E b v (e.symm x) := by
  change (1 : ℂ) * BoundedHolderSpace.physical E b v (e.symm x) = _
  exact one_mul _

variable (hV : IsCompact (closure V)) (hW : IsCompact (closure W))

theorem graphMap_smooth (c : SmoothSupportedManifoldCore.core (E := E) V) :
    graphMap e hb (EuclideanSmoothHolderCore.core hV hb hb1 c) =
      EuclideanSmoothHolderCore.core hW hb hb1 (smoothCore e cover c) := by
  apply BoundedHolderSpace.physical_injective F b
  ext x
  rw [graphMap_physical]
  rfl

include cover in
theorem maps_little (v : EuclideanSmoothHolderCore.space hV hb hb1) :
    graphMap e hb v.val ∈ EuclideanSmoothHolderCore.space hW hb hb1 := by
  refine (EuclideanSmoothHolderCore.smooth_dense hV hb hb1).induction_on
    (p := fun z => graphMap e hb z.val ∈ EuclideanSmoothHolderCore.space hW hb hb1) v ?_ ?_
  · exact (Submodule.isClosed_topologicalClosure _).preimage
      ((graphMap e hb).continuous.comp continuous_subtype_val)
  · intro c
    change graphMap e hb (EuclideanSmoothHolderCore.core hV hb hb1 c) ∈ _
    rw [graphMap_smooth e cover hb hb1 hV hW]
    exact Submodule.le_topologicalClosure _ ⟨smoothCore e cover c,rfl⟩

def operator : EuclideanSmoothHolderCore.space hV hb hb1 →L[ℂ]
    EuclideanSmoothHolderCore.space hW hb hb1 :=
  ((graphMap e hb).comp (EuclideanSmoothHolderCore.space hV hb hb1).subtypeL).codRestrict
    (EuclideanSmoothHolderCore.space hW hb hb1) (maps_little e cover hb hb1 hV hW)

theorem physical_operator (v : EuclideanSmoothHolderCore.space hV hb hb1) (x : F) :
    EuclideanSmoothHolderCore.physical hW hb hb1 (operator e cover hb hb1 hV hW v) x =
      EuclideanSmoothHolderCore.physical hV hb hb1 v (e.symm x) :=
  graphMap_physical e hb v.val x

end LeanShared.LittleHolderLinearPrecomposition
