module
public import LeanShared.Geometry.FractionalDerivativePredecessor
public import LeanShared.Analysis.LocalSmoothHolder
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Actual local n-th derivative Holder jets, used to prove all-order
fractional chart transport. Germ invariance and differentiation are proved;
no higher fractional chain-rule package is assumed. -/
public noncomputable section
namespace LeanShared.FractionalManifoldRegularity
open Set Filter
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

structure JetAt (n : ℕ) (a : ℝ) (f : E → F) (x : E) : Prop where
  smooth : ContDiffAt ℝ n f x
  holder : ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ y ∈ U, ∀ z ∈ U, ‖iteratedFDeriv ℝ n f y-iteratedFDeriv ℝ n f z‖ ≤ C*‖y-z‖^a

namespace JetAt
variable {n : ℕ} {a : ℝ} {f g : E → F} {x : E}

theorem congr (hf : JetAt n a f x) (equal : f =ᶠ[𝓝 x] g) : JetAt n a g x := by
  obtain ⟨U,openU,inU,C,hC,bound⟩ := hf.holder
  obtain ⟨O,subO,openO,inO⟩ := mem_nhds_iff.mp (equal.iteratedFDeriv ℝ n)
  refine ⟨hf.smooth.congr_of_eventuallyEq equal.symm,
    U∩O,openU.inter openO,⟨inU,inO⟩,C,hC,?_⟩
  intro y hy z hz
  rw [←subO hy.2,←subO hz.2]
  exact bound y hy.1 z hz.1

theorem derivative (hf : JetAt (n+1) a f x) : JetAt n a (fderiv ℝ f) x := by
  obtain ⟨U,openU,inU,C,hC,bound⟩ := hf.holder
  refine ⟨hf.smooth.fderiv_right (by simp only [Nat.cast_add,Nat.cast_one]; exact le_rfl),
    U,openU,inU,C,hC,?_⟩
  intro y hy z hz
  rw [←norm_iterated_difference_succ]
  exact bound y hy z hz

theorem of_derivative (smooth : ContDiffAt ℝ (n+1) f x)
    (hf : JetAt n a (fderiv ℝ f) x) : JetAt (n+1) a f x := by
  obtain ⟨U,openU,inU,C,hC,bound⟩ := hf.holder
  refine ⟨smooth,U,openU,inU,C,hC,?_⟩
  intro y hy z hz
  rw [norm_iterated_difference_succ]
  exact bound y hy z hz

/-- One extra ordinary derivative genuinely controls every subunit Holder
exponent on the top derivative, on a constructed neighborhood. -/
theorem of_contDiff_succ (ha1 : a ≤ 1) (hf : ContDiffAt ℝ (n+1) f x) : JetAt n a f x := by
  have top : ContDiffAt ℝ 1 (iteratedFDeriv ℝ n f) x :=
    hf.iteratedFDeriv_right (by exact le_of_eq (add_comm _ _))
  obtain ⟨U,openU,inU,_inside,C,hC,bound⟩ := LocalSmoothHolder.exists_holder_on top ha1 (Filter.univ_mem (α := E))
  refine ⟨hf.of_le (by exact_mod_cast (Nat.le_succ n)),U,openU,inU,C,hC,bound⟩

end JetAt
end LeanShared.FractionalManifoldRegularity
