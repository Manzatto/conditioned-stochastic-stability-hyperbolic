module
public import LeanShared.Analysis.ContinuousIdempotentOrthogonalization
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-! Two genuine projection ranges with invertible difference reconstruct
the complementary oblique projection, with exact range and kernel. -/
public noncomputable section
namespace LeanShared.ComplementaryProjectionReconstruction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

@[expose] def reconstruct (R S : E →L[ℝ] E) : E →L[ℝ] E := R*Ring.inverse (R-S)

omit [FiniteDimensional ℝ E] in
theorem properties (R S : E →L[ℝ] E) (hR : IsIdempotentElem R) (hS : IsIdempotentElem S)
    (unit : IsUnit (R-S)) : IsIdempotentElem (reconstruct R S) ∧
      (reconstruct R S).range=R.range ∧ (reconstruct R S).ker=S.range := by
  let D := R-S
  let B := Ring.inverse D
  have left : B*D=1 := Ring.inverse_mul_cancel D unit
  have right : D*B=1 := Ring.mul_inverse_cancel D unit
  have RD : R*D=D*(1-S) := by dsimp only [D]; noncomm_ring [hR.eq,hS.eq]
  have SD : S*D=D*(1-R) := by dsimp only [D]; noncomm_ring [hR.eq,hS.eq]
  have moveR : B*R=(1-S)*B := by
    calc
      _ = (B*R)*(D*B) := by rw [right,mul_one]
      _ = B*(R*D)*B := by noncomm_ring
      _ = B*(D*(1-S))*B := by rw [RD]
      _ = (1-S)*B := by rw [← mul_assoc B D (1-S),left,one_mul]
  have moveS : B*S=(1-R)*B := by
    calc
      _ = (B*S)*(D*B) := by rw [right,mul_one]
      _ = B*(S*D)*B := by noncomm_ring
      _ = B*(D*(1-R))*B := by rw [SD]
      _ = (1-R)*B := by rw [← mul_assoc B D (1-R),left,one_mul]
  have BR : (R*B)*R=R := by
    calc
      _ = R*((1-S)*B) := by rw [mul_assoc,moveR]
      _ = (R*D)*B := by dsimp only [D]; noncomm_ring [hR.eq]
      _ = R := by rw [mul_assoc,right,mul_one]
  have BS : (R*B)*S=0 := by rw [mul_assoc,moveS,← mul_assoc]; noncomm_ring [hR.eq]
  have complement : 1-R*B= -S*B := by
    have fact := right
    dsimp only [D] at fact
    noncomm_ring [← fact]
  have idem : IsIdempotentElem (reconstruct R S) := by
    change (R*B)*(R*B)=R*B
    rw [← mul_assoc,BR]
  refine ⟨idem,?_,?_⟩
  · ext v
    constructor
    · rintro ⟨w,rfl⟩
      exact ⟨B w,rfl⟩
    · rintro ⟨w,rfl⟩
      refine ⟨R w,?_⟩
      exact congrArg (fun L : E →L[ℝ] E => L w) BR
  · ext v
    constructor
    · intro hv
      have identity := congrArg (fun L : E →L[ℝ] E => L v) complement
      change v-reconstruct R S v= -(S (B v)) at identity
      rw [show reconstruct R S v=0 from hv,sub_zero] at identity
      refine ⟨-B v,?_⟩
      rw [map_neg]
      exact identity.symm
    · rintro ⟨w,rfl⟩
      exact congrArg (fun L : E →L[ℝ] E => L w) BS

/-- Orthogonal projections onto the actual range and kernel of an
idempotent have invertible difference. -/
theorem range_kernel_difference_isUnit (P : E →L[ℝ] E) (idem : IsIdempotentElem P) :
    IsUnit (P.range.starProjection-P.ker.starProjection) := by
  let R := P.range.starProjection
  let S := P.ker.starProjection
  have zero (v : E) (hv : (R-S) v=0) : v=0 := by
    have equal : R v=S v := sub_eq_zero.mp hv
    have memberRange : R v ∈ P.range := P.range.starProjection_apply_mem v
    have memberKernel : R v ∈ P.ker := equal ▸ P.ker.starProjection_apply_mem v
    obtain ⟨w,hw⟩ := memberRange
    have fixed : P (R v)=R v := by rw [← hw]; exact congrArg (fun L : E →L[ℝ] E => L w) idem.eq
    have rzero : R v=0 := fixed.symm.trans memberKernel
    have szero : S v=0 := equal.symm.trans rzero
    have kerMember : v-P v ∈ P.ker := by
      change P (v-P v)=0
      rw [map_sub,show P (P v)=P v from congrArg (fun L : E →L[ℝ] E => L v) idem.eq,sub_self]
    have first := P.range.starProjection_inner_eq_zero v (P v) (show P v ∈ P.range from ⟨v,rfl⟩)
    have second := P.ker.starProjection_inner_eq_zero v (v-P v) kerMember
    change inner ℝ (v-R v) (P v)=0 at first
    change inner ℝ (v-S v) (v-P v)=0 at second
    rw [rzero,sub_zero] at first
    rw [szero,sub_zero] at second
    have innerZero : inner ℝ v v=0 := by
      have sum := (inner_add_right v (P v) (v-P v)).trans (by rw [first,second,add_zero])
      simpa only [add_sub_cancel] using sum
    exact inner_self_eq_zero.mp innerZero
  have injective : Function.Injective (R-S) := by
    intro u v equal
    apply sub_eq_zero.mp
    apply zero
    rw [map_sub,equal,sub_self]
  let e := (R-S).toLinearMap.linearEquivOfInjective injective rfl
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨injective,fun v => ⟨e.symm v,e.apply_symm_apply v⟩⟩
theorem fixes (P : E →L[ℝ] E) (idem : IsIdempotentElem P) :
    reconstruct P.range.starProjection P.ker.starProjection=P := by
  have result := properties P.range.starProjection P.ker.starProjection
    P.range.isIdempotentElem_starProjection P.ker.isIdempotentElem_starProjection
    (range_kernel_difference_isUnit P idem)
  apply (ContinuousLinearMap.IsIdempotentElem.ext_iff result.1 idem).mpr
  exact ⟨result.2.1.trans P.range.range_starProjection,
    result.2.2.trans P.ker.range_starProjection⟩
end LeanShared.ComplementaryProjectionReconstruction
