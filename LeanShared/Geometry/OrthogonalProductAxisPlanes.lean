module
public import LeanShared.Analysis.SplitCoordinateOrthogonalSlopes
public import LeanShared.Analysis.OrthogonalDiagonalConeBounds

/-! The two fixed axes in the genuine Hilbert model have exactly the
projection matrices used by the adapted cone estimates. -/
@[expose] public noncomputable section
namespace LeanShared.OrthogonalProductCoordinates
open Set SplitCoordinateOrthogonalSlopes
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

def firstPlane (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) : Submodule ℝ E :=
  unstablePlane (equiv dimension)

def secondPlane (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) : Submodule ℝ E :=
  stablePlane (equiv dimension)

theorem firstPlane_dimension (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) :
    Module.finrank ℝ (firstPlane dimension) = Module.finrank ℝ X := by
  unfold firstPlane unstablePlane
  rw [(equiv dimension).toLinearEquiv.finrank_map_eq,(Submodule.prodEquiv _ _).finrank_eq]
  simp [Module.finrank_prod]

theorem secondPlane_dimension (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) :
    Module.finrank ℝ (secondPlane dimension) = Module.finrank ℝ Y := by
  unfold secondPlane stablePlane
  rw [(equiv dimension).toLinearEquiv.finrank_map_eq,(Submodule.prodEquiv _ _).finrank_eq]
  simp [Module.finrank_prod]

theorem secondPlane_eq_orthogonal (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) :
    secondPlane dimension = (firstPlane dimension)ᗮ := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro v member
    obtain ⟨z,hz,rfl⟩ := member
    have zeroFirst : z.1=0 := hz.1
    rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨w,hw,rfl⟩ := hu
    have zeroSecond : w.2=0 := hw.2
    have wEq : w=(w.1,0) := Prod.ext rfl zeroSecond
    have zEq : z=(0,z.2) := Prod.ext zeroFirst rfl
    change inner ℝ (equiv dimension w) (equiv dimension z)=0
    rw [wEq,zEq]
    exact axes_inner dimension w.1 z.2
  · have total := (firstPlane dimension).finrank_add_finrank_orthogonal
    rw [firstPlane_dimension] at total
    rw [secondPlane_dimension]
    have dims := dimension
    rw [Module.finrank_prod] at dims
    omega

theorem firstPlane_projection (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) :
    (firstPlane dimension).starProjection = firstProjection dimension := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨z,rfl⟩ := (equiv dimension).surjective v
  rw [firstProjection_apply]
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact Submodule.mem_map.mpr ⟨(z.1,0),by simp,rfl⟩
  · rw [←secondPlane_eq_orthogonal]
    have residual : equiv dimension z-equiv dimension (z.1,0)=equiv dimension (0,z.2) := by
      rw [←map_sub]
      exact congrArg (equiv dimension) (Prod.ext (sub_self _) (sub_zero _))
    rw [residual]
    exact Submodule.mem_map.mpr ⟨(0,z.2),by simp,rfl⟩

theorem orthogonal_firstPlane_projection (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) :
    (firstPlane dimension)ᗮ.starProjection = secondProjection dimension := by
  apply ContinuousLinearMap.ext
  intro v
  have sum := (firstPlane dimension).starProjection_add_starProjection_orthogonal v
  rw [firstPlane_projection] at sum
  have model := projections_add dimension v
  exact add_left_cancel (sum.trans (by simpa only [add_comm] using model.symm))

end LeanShared.OrthogonalProductCoordinates
