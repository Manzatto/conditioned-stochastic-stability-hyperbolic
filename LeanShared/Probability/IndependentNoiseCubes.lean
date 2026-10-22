module

public import LeanShared.Probability.NoiseCubeRescaling
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! Independent controls are exactly the ordinary cube on the disjoint union
of their coordinate indices. The identification preserves restricted Lebesgue
volume, rather than introducing a different reference density. -/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LeanShared.NoiseCubeRescaling

variable {ι κ : Type*}

def splitCube (ε : ℝ) : cube (ι := ι ⊕ κ) ε ≃ₜ
    cube (ι := ι) ε × cube (ι := κ) ε where
  toFun v := (⟨fun i => v.val (.inl i), fun i => v.property (.inl i)⟩,
    ⟨fun j => v.val (.inr j), fun j => v.property (.inr j)⟩)
  invFun v := ⟨Sum.elim v.1.val v.2.val, fun i => by
    cases i with
    | inl i => exact v.1.property i
    | inr j => exact v.2.property j⟩
  left_inv v := by ext i; cases i <;> rfl
  right_inv v := by ext <;> rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_pi fun i => (continuous_apply (Sum.inl i : ι ⊕ κ)).comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact continuous_pi fun i => (continuous_apply (Sum.inr i : ι ⊕ κ)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    cases i with
    | inl i => exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
    | inr i => exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)

@[simp] theorem splitCube_left (ε : ℝ) (v : cube (ι := ι ⊕ κ) ε) (i : ι) :
    ((splitCube ε v).1).val i = v.val (.inl i) := rfl

@[simp] theorem splitCube_right (ε : ℝ) (v : cube (ι := ι ⊕ κ) ε) (i : κ) :
    ((splitCube ε v).2).val i = v.val (.inr i) := rfl

variable [Fintype ι] [Fintype κ]

def cubeVolume (ε : ℝ) : Measure (cube (ι := ι) ε) :=
  (volume : Measure (ι → ℝ)).comap Subtype.val

instance cubeVolume_finite (ε : ℝ) : IsFiniteMeasure (cubeVolume (ι := ι) ε) := by
  constructor
  change ((volume : Measure (ι → ℝ)).comap Subtype.val) univ < ∞
  rw [comap_subtype_coe_apply (cube_compact ε).measurableSet]
  simpa only [Set.image_univ, Subtype.range_coe] using
    (cube_compact (ι := ι) ε).measure_lt_top (μ := (volume : Measure (ι → ℝ)))

/-- Splitting coordinates preserves the literal restricted Lebesgue measure. -/
theorem splitCube_volume (ε : ℝ) :
    (cubeVolume (ι := ι ⊕ κ) ε).map (splitCube ε) =
      (cubeVolume (ι := ι) ε).prod (cubeVolume (ι := κ) ε) := by
  let : IsFiniteMeasure ((volume : Measure (ι → ℝ)).comap
      (Subtype.val : cube (ι := ι) ε → ι → ℝ)) := cubeVolume_finite ε
  let : IsFiniteMeasure ((volume : Measure (κ → ℝ)).comap
      (Subtype.val : cube (ι := κ) ε → κ → ℝ)) := cubeVolume_finite ε
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => ℝ)
  let f : cube (ι := ι) ε × cube (ι := κ) ε → (ι → ℝ) × (κ → ℝ) :=
    Prod.map Subtype.val Subtype.val
  have hi : MeasurableEmbedding f :=
    (MeasurableEmbedding.subtype_coe (cube_compact ε).measurableSet).prodMap
      (MeasurableEmbedding.subtype_coe (cube_compact ε).measurableSet)
  apply hi.map_injective
  rw [Measure.map_map hi.measurable (splitCube ε).measurable]
  have hcomp : f ∘ splitCube ε = e ∘ (Subtype.val : cube (ι := ι ⊕ κ) ε → _) := rfl
  rw [hcomp, ← Measure.map_map e.measurable measurable_subtype_coe]
  rw [cubeVolume, map_comap_subtype_coe (cube_compact ε).measurableSet]
  have hpre : e ⁻¹' (cube (ι := ι) ε ×ˢ cube (ι := κ) ε) = cube (ι := ι ⊕ κ) ε := by
    ext v
    change ((∀ i, |v (.inl i)| ≤ ε) ∧ ∀ j, |v (.inr j)| ≤ ε) ↔ ∀ k, |v k| ≤ ε
    constructor
    · rintro ⟨hl, hr⟩ (i | j)
      · exact hl i
      · exact hr j
    · intro h
      exact ⟨fun i => h (.inl i), fun j => h (.inr j)⟩
  rw [← hpre, ← Measure.restrict_map e.measurable
    ((cube_compact ε).measurableSet.prod (cube_compact ε).measurableSet)]
  rw [(volume_measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ κ => ℝ)).map_eq]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [← map_comap_subtype_coe (cube_compact ε).measurableSet,
    ← map_comap_subtype_coe (cube_compact ε).measurableSet]
  exact Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe


/-- The reverse identification transports independent reference volumes back
onto the literal sum-coordinate cube. -/
theorem splitCube_symm_volume (ε : ℝ) :
    ((cubeVolume (ι := ι) ε).prod (cubeVolume (ι := κ) ε)).map (splitCube ε).symm =
      cubeVolume (ι := ι ⊕ κ) ε := by
  rw [← splitCube_volume, Measure.map_map (splitCube ε).symm.measurable (splitCube ε).measurable]
  simp only [Function.comp_def, Homeomorph.symm_apply_apply, Measure.map_id']

end LeanShared.NoiseCubeRescaling

namespace LeanShared

/-- An exact density formula for an invertible continuous reparametrization.
Only ordinary measurability is used. -/
theorem Homeomorph.map_withDensity {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] (e : X ≃ₜ Y) (ν : Measure X)
    (p : X → ℝ≥0∞) (hp : Measurable p) :
    (ν.withDensity p).map e = (ν.map e).withDensity (p ∘ e.symm) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf e.measurable,
    lintegral_withDensity_eq_lintegral_mul ν hp (g := fun x => f (e x))
      (hf.comp e.measurable),
    lintegral_withDensity_eq_lintegral_mul (ν.map e) (hp.comp e.symm.measurable) hf]
  simp only [Pi.mul_apply, Function.comp_def]
  rw [lintegral_map (f := fun y => p (e.symm y) * f y)
      ((hp.comp e.symm.measurable).mul hf) e.measurable]
  simp only [Homeomorph.symm_apply_apply]

end LeanShared

