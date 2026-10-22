module
public import LeanShared.Geometry.FractionalDerivativeSuccessor

/-! Differentiating an actual fractional C^(r+1) function gives actual C^r
regularity; all derivative-tensor identifications are proved by currying. -/
public noncomputable section
open Set
open scoped Manifold ContDiff
namespace LeanShared.FractionalManifoldRegularity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem regular_fderiv_of_regular {f : E → F} {r : ℝ} (hr : 0≤r)
    (regular : Regular (E:=E) (F:=F) (r+1) f) :
    Regular (E:=E) (F:=E →L[ℝ] F) r (fderiv ℝ f) := by
  have floor : ⌊r+1⌋₊=⌊r⌋₊+1 := Nat.floor_add_one hr
  refine ⟨hr,?_,?_⟩
  · have original : ContDiff ℝ ((⌊r⌋₊:ℕ∞ω)+1) f := by
      have smooth := regular.differentiable.contDiff
      simpa only [floor,Nat.cast_add,Nat.cast_one] using smooth
    exact (contDiff_succ_iff_fderiv.mp original).2.2.contMDiff
  · intro unequal x
    have unequalHigher : r+1≠(⌊r+1⌋₊:ℝ) := by
      intro equal
      rw [floor,Nat.cast_add,Nat.cast_one] at equal
      exact unequal (by linarith)
    obtain ⟨U,openU,inside,_,C,hC,bound⟩ := regular.holder unequalHigher x
    have chartF : chartMap (E:=E) (F:=F) f x=f := by simp [chartMap,chartAt_self_eq]
    have chartD : chartMap (E:=E) (F:=E →L[ℝ] F) (fderiv ℝ f) x=fderiv ℝ f := by
      simp [chartMap,chartAt_self_eq]
    have domain : chartDomain (E:=E) (F:=E →L[ℝ] F) (fderiv ℝ f) x=univ := by
      simp [chartDomain,chartAt_self_eq]
    refine ⟨U,openU,inside,?_,C,hC,?_⟩
    · rw [domain]
      exact subset_univ _
    · intro y hy z hz
      rw [chartD,←norm_iterated_difference_succ]
      have estimate := bound y hy z hz
      rw [floor,chartF] at estimate
      have exponent : r+1-((⌊r⌋₊+1:ℕ):ℝ)=r-(⌊r⌋₊:ℝ) := by
        rw [Nat.cast_add,Nat.cast_one]
        ring
      rw [exponent] at estimate
      exact estimate
end LeanShared.FractionalManifoldRegularity
