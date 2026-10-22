module
public import LeanShared.Analysis.FakeLeafGeometry
public import LeanShared.Analysis.ProjectionConeTransversality

/-! Explicit secant constants for the actual half-aperture normal cone.
The infimum defining a fake leaf need not be attained. -/
public noncomputable section
namespace LeanShared.ProjectionConeFakeLeafSlope
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem normal_projection (U : Submodule ℝ E) (v : E)
    (member : v ∈ ProjectionConeTransversality.cone U.starProjection (1/2)) :
    (2/3:ℝ)*‖v‖ ≤ ‖Uᗮ.starProjection v‖ := by
  change ‖U.starProjection v‖ ≤ (1/2:ℝ)*‖v-U.starProjection v‖ at member
  have cone : ‖U.starProjection v‖ ≤ (1/2:ℝ)*‖Uᗮ.starProjection v‖ := by
    simpa only [Submodule.starProjection_orthogonal, sub_apply,
      ContinuousLinearMap.id_apply] using member
  have triangle : ‖v‖ ≤ ‖U.starProjection v‖+‖Uᗮ.starProjection v‖ := by
    simpa only [U.starProjection_add_starProjection_orthogonal] using
      norm_add_le (U.starProjection v) (Uᗮ.starProjection v)
  linarith

theorem half_cone_secants (U : Submodule ℝ E)
    (positive : 0 < Module.finrank ℝ Uᗮ) (Γ : Set E)
    (fake : FakeLeafGeometry.leafError
      (ProjectionConeTransversality.cone U.starProjection (1/2))
      (Module.finrank ℝ Uᗮ) Γ = 0) :
    ∀x∈Γ,∀y∈Γ, ‖Uᗮ.starProjection (x-y)‖ ≤ (3/2:ℝ)*‖U.starProjection (x-y)‖ := by
  let C := ProjectionConeTransversality.cone U.starProjection (1/2)
  have planes : (FakeLeafGeometry.admissiblePlanes C (Module.finrank ℝ Uᗮ)).Nonempty := by
    refine ⟨Uᗮ, ?_, rfl⟩
    intro v member
    have zero : U.starProjection v=0 :=
      Submodule.eq_starProjection_of_mem_orthogonal U.zero_mem (by simpa using member)
    change ‖U.starProjection v‖ ≤ (1/2:ℝ)*‖v-U.starProjection v‖
    rw [zero,norm_zero]
    positivity
  intro x hx y hy
  by_cases same : x=y
  · simp [same]
  have normal := FakeLeafGeometry.normalError_eq_zero_of_leafError_zero positive planes fake
    hy hx (Ne.symm same)
  have bound := ConeGraphGeometry.stable_projection_le_of_arbitrarily_approximately_orthogonal
    U (by norm_num : (0:ℝ)<2/3) (fun v hv => normal_projection U v hv) (x-y) (by
      intro ε hε
      exact FakeLeafGeometry.exists_approximate_normal_plane planes (x-y) normal hε)
  norm_num at bound ⊢
  exact bound

/-- Transport a fixed-plane secant estimate to the actual nearby plane.
Both the error and longitudinal loss are retained explicitly. -/
theorem transport (V U : Submodule ℝ E) (z : E) {L δ K : ℝ}
    (nonnegativeL : 0≤L) (nonnegativeδ : 0≤δ)
    (close : ‖V.starProjection-U.starProjection‖≤δ)
    (slope : ‖Vᗮ.starProjection z‖≤L*‖V.starProjection z‖)
    (small : δ*(1+L)<1)
    (constant : L+δ*(1+L)≤K*(1-δ*(1+L))) :
    ‖Uᗮ.starProjection z‖≤K*‖U.starProjection z‖ := by
  have positiveK : 0≤K := by
    have denom : 0<1-δ*(1+L) := sub_pos.mpr small
    nlinarith [mul_nonneg nonnegativeδ (show 0≤1+L by linarith)]
  have total : ‖z‖≤(1+L)*‖V.starProjection z‖ := by
    have triangle : ‖z‖≤‖V.starProjection z‖+‖Vᗮ.starProjection z‖ := by
      simpa only [V.starProjection_add_starProjection_orthogonal] using
        norm_add_le (V.starProjection z) (Vᗮ.starProjection z)
    linarith
  have error : ‖V.starProjection z-U.starProjection z‖≤δ*‖z‖ :=
    ((V.starProjection-U.starProjection).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right close (norm_nonneg z))
  have longitudinal : (1-δ*(1+L))*‖V.starProjection z‖≤‖U.starProjection z‖ := by
    have triangle := norm_sub_norm_le (V.starProjection z) (U.starProjection z)
    have scaled := mul_le_mul_of_nonneg_left total nonnegativeδ
    nlinarith
  have transverse : ‖Uᗮ.starProjection z‖≤(L+δ*(1+L))*‖V.starProjection z‖ := by
    have identity : Uᗮ.starProjection z = Vᗮ.starProjection z+
        (V.starProjection z-U.starProjection z) := by
      rw [U.starProjection_orthogonal,V.starProjection_orthogonal]
      simp only [sub_apply,ContinuousLinearMap.id_apply]
      abel
    have triangle := norm_add_le (Vᗮ.starProjection z) (V.starProjection z-U.starProjection z)
    rw [←identity] at triangle
    have scaled := mul_le_mul_of_nonneg_left total nonnegativeδ
    nlinarith
  calc
    _ ≤ (L+δ*(1+L))*‖V.starProjection z‖ := transverse
    _ ≤ (K*(1-δ*(1+L)))*‖V.starProjection z‖ :=
      mul_le_mul_of_nonneg_right constant (norm_nonneg _)
    _ = K*((1-δ*(1+L))*‖V.starProjection z‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left longitudinal positiveK

end LeanShared.ProjectionConeFakeLeafSlope
