module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.CompMap
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Kernels on a measurable survival subtype

Pulling a kernel back to a measurable subtype restricts its destination
measure to that set. When the ambient kernel already takes values supported
there, every power agrees after inclusion into the ambient state space.
No probability or regularity assumptions are needed for these identities.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LeanShared.SubtypeKernel

variable {X : Type*} [MeasurableSpace X]

/-- Source and destination restriction to a measurable live-state subtype. -/
def restrict (K : Kernel X X) (U : Set X) (hU : MeasurableSet U) : Kernel U U :=
  (K.comap Subtype.val measurable_subtype_coe).comapRight
    (MeasurableEmbedding.subtype_coe hU)

@[simp]
theorem restrict_apply (K : Kernel X X) (U : Set X) (hU : MeasurableSet U) (x : U) :
    restrict K U hU x = (K x.val).comap Subtype.val := rfl

/-- The live kernel is literally the ambient measure pulled back by inclusion. -/
theorem restrict_apply_set (K : Kernel X X) (U : Set X) (hU : MeasurableSet U)
    (x : U) (A : Set U) (hA : MeasurableSet A) :
    restrict K U hU x A = K x.val (Subtype.val '' A) := by
  exact Kernel.comapRight_apply' _ _ _ hA

/-- Pushing the live measure into the ambient type gives the destination restriction. -/
theorem map_restrict_apply (K : Kernel X X) (U : Set X) (hU : MeasurableSet U) (x : U) :
    (restrict K U hU x).map Subtype.val = (K x.val).restrict U := by
  rw [restrict_apply, map_comap_subtype_coe hU]

theorem restrict_mass_le_one (K : Kernel X X) (U : Set X) (hU : MeasurableSet U)
    (hK : ∀ x, K x univ ≤ 1) (x : U) : restrict K U hU x univ ≤ 1 := by
  rw [restrict_apply_set _ _ _ _ _ MeasurableSet.univ, Set.image_univ, Subtype.range_coe]
  exact (measure_mono (subset_univ U)).trans (hK x.val)

/-- Zero extension of an observable defined only on the live states. -/
def zeroExtend (U : Set X) (f : U → ℝ) : X → ℝ :=
  Function.extend Subtype.val f (fun _ => 0)

omit [MeasurableSpace X] in
@[simp]
theorem zeroExtend_coe (U : Set X) (f : U → ℝ) (x : U) :
    zeroExtend U f x.val = f x :=
  Subtype.val_injective.extend_apply _ _ _

omit [MeasurableSpace X] in
theorem zeroExtend_of_not_mem (U : Set X) (f : U → ℝ) (x : X) (hx : x ∉ U) :
    zeroExtend U f x = 0 := by
  apply Function.extend_apply'
  rintro ⟨y, rfl⟩
  exact hx y.property

omit [MeasurableSpace X] in
/-- A nonnegative upper bound is preserved under zero extension. -/
theorem zeroExtend_le (U : Set X) (f : U → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ x, f x ≤ B) (x : X) : zeroExtend U f x ≤ B := by
  by_cases hx : x ∈ U
  · have he := zeroExtend_coe U f ⟨x, hx⟩
    change zeroExtend U f x = f ⟨x, hx⟩ at he
    rw [he]
    exact hf ⟨x, hx⟩
  · rw [zeroExtend_of_not_mem U f x hx]
    exact hB

omit [MeasurableSpace X] in
/-- A uniform norm bound is preserved under zero extension. -/
theorem norm_zeroExtend_le (U : Set X) (f : U → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ x, ‖f x‖ ≤ B) (x : X) : ‖zeroExtend U f x‖ ≤ B := by
  by_cases hx : x ∈ U
  · have he := zeroExtend_coe U f ⟨x, hx⟩
    change zeroExtend U f x = f ⟨x, hx⟩ at he
    rw [he]
    exact hf ⟨x, hx⟩
  · rw [zeroExtend_of_not_mem U f x hx, norm_zero]
    exact hB

@[fun_prop]
theorem measurable_zeroExtend (U : Set X) (hU : MeasurableSet U)
    (f : U → ℝ) (hf : Measurable f) : Measurable (zeroExtend U f) :=
  (MeasurableEmbedding.subtype_coe hU).measurable_extend hf measurable_const

/-- Integration of a subtype-only observable uses its zero extension. -/
theorem integral_restrict (K : Kernel X X) (U : Set X) (hU : MeasurableSet U)
    (f : U → ℝ) (x : U) :
    (∫ y, f y ∂restrict K U hU x) = ∫ y in U, zeroExtend U f y ∂K x.val := by
  rw [restrict_apply, ← integral_subtype_comap hU]
  simp only [zeroExtend_coe]

/-- Ambient integration agrees with live integration for a supported kernel.
The measurable embedding theorem covers totalized Bochner integrals too. -/
theorem integral_restrict_supported (K : Kernel X X) (U : Set X) (hU : MeasurableSet U)
    (hKU : ∀ x, (K x).restrict U = K x) (f : X → ℝ) (x : U) :
    (∫ y, f y.val ∂restrict K U hU x) = ∫ y, f y ∂K x.val := by
  rw [← (MeasurableEmbedding.subtype_coe hU).integral_map f,
    map_restrict_apply, hKU]

/-- The subtype restriction intertwines all powers with a supported ambient kernel. -/
theorem map_restrict_pow (K : Kernel X X) (U : Set X) (hU : MeasurableSet U)
    (hKU : ∀ x, (K x).restrict U = K x) (n : ℕ) :
    (restrict K U hU ^ n).map Subtype.val = (K ^ n).comap Subtype.val measurable_subtype_coe := by
  have hstep : (restrict K U hU).map Subtype.val =
      K.comap Subtype.val measurable_subtype_coe := by
    ext x A hA
    rw [Kernel.map_apply _ measurable_subtype_coe, map_restrict_apply, hKU]
    rfl
  induction n with
  | zero =>
      ext x A hA
      have hIU : (1 : Kernel U U) = Kernel.id := by rfl
      have hIX : (1 : Kernel X X) = Kernel.id := by rfl
      rw [pow_zero, pow_zero, hIU, hIX, Kernel.map_apply _ measurable_subtype_coe,
        Kernel.id_apply, Measure.map_dirac' measurable_subtype_coe,
        Kernel.comap_apply, Kernel.id_apply]
  | succ n ih =>
      rw [Nat.add_comm n 1, Kernel.pow_add, Kernel.pow_add, pow_one, pow_one]
      rw [Kernel.map_comp, hstep, ← Kernel.comp_map _ _ measurable_subtype_coe, ih]
      ext x A hA
      rw [Kernel.comp_apply' _ _ _ hA, Kernel.comap_apply,
        Kernel.comap_apply, Kernel.comp_apply' _ _ _ hA]

/-- At each horizon, inclusion pushes the live endpoint law to the ambient law. -/
theorem map_restrict_pow_apply (K : Kernel X X) (U : Set X) (hU : MeasurableSet U)
    (hKU : ∀ x, (K x).restrict U = K x) (n : ℕ) (x : U) :
    ((restrict K U hU ^ n) x).map Subtype.val = (K ^ n) x.val := by
  have he := congrArg (fun L : Kernel U X => L x) (map_restrict_pow K U hU hKU n)
  simpa only [Kernel.map_apply _ measurable_subtype_coe, Kernel.comap_apply] using he

end LeanShared.SubtypeKernel
