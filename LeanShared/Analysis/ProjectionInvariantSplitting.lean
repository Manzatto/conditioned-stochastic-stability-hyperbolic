module
public import Mathlib.LinearAlgebra.Projection

/-! An invariant range and kernel determine the projection intertwining
identity. No commutation hypothesis or invertibility of the transporter is
needed. -/
public section
namespace LeanShared.ProjectionInvariantSplitting

theorem intertwines {𝕜 H K : Type*} [Field 𝕜]
    [AddCommGroup H] [Module 𝕜 H] [AddCommGroup K] [Module 𝕜 K]
    (P : H →ₗ[𝕜] H) (Q : K →ₗ[𝕜] K) (A : H →ₗ[𝕜] K)
    (idemP : P.comp P = P) (idemQ : Q.comp Q = Q)
    (rangeInvariant : P.range.map A ≤ Q.range)
    (kernelInvariant : P.ker.map A ≤ Q.ker) : Q.comp A = A.comp P := by
  ext v
  have fixed : Q (A (P v)) = A (P v) := by
    obtain ⟨w, hw⟩ := rangeInvariant (Submodule.mem_map.mpr
      ⟨P v, LinearMap.mem_range.mpr ⟨v, rfl⟩, rfl⟩)
    rw [← hw]
    exact congrArg (fun L : K →ₗ[𝕜] K => L w) idemQ
  have killed : Q (A (v - P v)) = 0 := by
    apply kernelInvariant
    refine Submodule.mem_map.mpr ⟨v - P v, ?_, rfl⟩
    change P (v - P v) = 0
    rw [map_sub, show P (P v) = P v from congrArg (fun L : H →ₗ[𝕜] H => L v) idemP,
      sub_self]
  change Q (A v) = A (P v)
  rw [map_sub, map_sub, fixed, sub_eq_zero] at killed
  exact killed

end LeanShared.ProjectionInvariantSplitting
