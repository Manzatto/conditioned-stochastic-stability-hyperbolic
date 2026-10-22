module

public import LeanShared.Analysis.ConeGraphGeometry
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The literal supremum--infimum condition for fake-leaf chords

The error is the signed supremum over nonzero normal-plane vectors, followed
by the infimum over admissible planes. Real planes contain both signs, making
the supremum nonnegative. Infimum zero therefore gives arbitrarily small
absolute normality errors, without an attained infimum or Grassmann compactness.
-/

@[expose] public noncomputable section

open Set

namespace LeanShared.FakeLeafGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normalized (v : E) : E := ‖v‖⁻¹ • v

@[simp] theorem normalized_zero : normalized (0 : E) = 0 := by simp [normalized]

theorem norm_normalized_le (v : E) : ‖normalized v‖ ≤ 1 := by
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  simp only [normalized, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ (ne_of_gt hn), le_refl]

@[simp] theorem normalized_neg (v : E) : normalized (-v) = -normalized v := by
  simp [normalized]

/-- The literal signed normalized values in Definition 5.10. -/
def planeErrorValues (P : Submodule ℝ E) (z : E) : Set ℝ :=
  {r | ∃ p ∈ P, p ≠ 0 ∧ r = inner ℝ (normalized z) (normalized p)}

def planeError (P : Submodule ℝ E) (z : E) : ℝ := sSup (planeErrorValues P z)

theorem planeErrorValues_le_one (P : Submodule ℝ E) (z : E) :
    ∀ r ∈ planeErrorValues P z, r ≤ 1 := by
  rintro r ⟨p, _, _, rfl⟩
  calc
    _ ≤ ‖normalized z‖ * ‖normalized p‖ := real_inner_le_norm _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_normalized_le z) (norm_normalized_le p)
      (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul _

theorem planeErrorValues_bddAbove (P : Submodule ℝ E) (z : E) :
    BddAbove (planeErrorValues P z) := ⟨1, planeErrorValues_le_one P z⟩

variable [FiniteDimensional ℝ E]

theorem planeErrorValues_nonempty (P : Submodule ℝ E) (z : E)
    (hdim : 0 < Module.finrank ℝ P) : (planeErrorValues P z).Nonempty := by
  obtain ⟨p, hp⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := P)).mp hdim
  refine ⟨_, p, p.property, ?_, rfl⟩
  exact fun h => hp (Subtype.ext h)

omit [FiniteDimensional ℝ E] in
theorem normalized_inner_le_planeError (P : Submodule ℝ E) (z : E)
    {p : E} (hp : p ∈ P) (hp0 : p ≠ 0) :
    inner ℝ (normalized z) (normalized p) ≤ planeError P z :=
  le_csSup (planeErrorValues_bddAbove P z) ⟨p, hp, hp0, rfl⟩

theorem planeError_nonneg (P : Submodule ℝ E) (z : E)
    (hdim : 0 < Module.finrank ℝ P) : 0 ≤ planeError P z := by
  obtain ⟨p, hp⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := P)).mp hdim
  have hp0 : (p : E) ≠ 0 := fun h => hp (Subtype.ext h)
  have hpos := normalized_inner_le_planeError P z p.property hp0
  have hneg := normalized_inner_le_planeError P z (P.neg_mem p.property) (neg_ne_zero.mpr hp0)
  rw [normalized_neg, inner_neg_right] at hneg
  linarith

theorem planeError_le_one (P : Submodule ℝ E) (z : E)
    (hdim : 0 < Module.finrank ℝ P) : planeError P z ≤ 1 :=
  csSup_le (planeErrorValues_nonempty P z hdim) (planeErrorValues_le_one P z)

/-- Cone-contained normal planes of the stipulated stable dimension. -/
def admissiblePlanes (C : Set E) (ds : ℕ) : Set (Submodule ℝ E) :=
  {P | (↑P : Set E) ⊆ C ∧ Module.finrank ℝ P = ds}

def normalErrorValues (C : Set E) (ds : ℕ) (z : E) : Set ℝ :=
  (fun P => planeError P z) '' admissiblePlanes C ds

/-- The literal infimum over admissible planes. -/
def normalError (C : Set E) (ds : ℕ) (z : E) : ℝ := sInf (normalErrorValues C ds z)

omit [FiniteDimensional ℝ E] in
theorem normalErrorValues_nonempty {C : Set E} {ds : ℕ}
    (hplanes : (admissiblePlanes C ds).Nonempty) (z : E) :
    (normalErrorValues C ds z).Nonempty := hplanes.image _

theorem normalErrorValues_nonneg (C : Set E) {ds : ℕ} (hds : 0 < ds) (z : E) :
    ∀ r ∈ normalErrorValues C ds z, 0 ≤ r := by
  rintro r ⟨P, hP, rfl⟩
  exact planeError_nonneg P z (hP.2.symm ▸ hds)

theorem normalErrorValues_bddBelow (C : Set E) {ds : ℕ} (hds : 0 < ds) (z : E) :
    BddBelow (normalErrorValues C ds z) := ⟨0, normalErrorValues_nonneg C hds z⟩

theorem normalError_nonneg {C : Set E} {ds : ℕ} (hds : 0 < ds)
    (hplanes : (admissiblePlanes C ds).Nonempty) (z : E) : 0 ≤ normalError C ds z := by
  apply le_csInf (normalErrorValues_nonempty hplanes z)
  exact (normalErrorValues_nonneg C hds z)

theorem normalError_le_one {C : Set E} {ds : ℕ} (hds : 0 < ds)
    (hplanes : (admissiblePlanes C ds).Nonempty) (z : E) : normalError C ds z ≤ 1 := by
  obtain ⟨P, hP⟩ := hplanes
  exact (csInf_le (normalErrorValues_bddBelow C hds z) ⟨P, hP, rfl⟩).trans
    (planeError_le_one P z (hP.2.symm ▸ hds))

omit [FiniteDimensional ℝ E] in
/-- Infimum zero supplies approximate planes, rather than a minimizing plane. -/
theorem exists_approximate_normal_plane {C : Set E} {ds : ℕ}
    (hplanes : (admissiblePlanes C ds).Nonempty) (z : E)
    (hzero : normalError C ds z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Submodule ℝ E, (↑P : Set E) ⊆ C ∧ Module.finrank ℝ P = ds ∧
      ∀ p ∈ P, |inner ℝ z p| ≤ ε * ‖z‖ * ‖p‖ := by
  have hlt : sInf (normalErrorValues C ds z) < ε := by rw [← normalError, hzero]; exact hε
  obtain ⟨r, ⟨P, hP, rfl⟩, hr⟩ :=
    exists_lt_of_csInf_lt (normalErrorValues_nonempty hplanes z) hlt
  refine ⟨P, hP.1, hP.2, ?_⟩
  apply ConeGraphGeometry.absolute_inner_bound_of_normalized_upper P z
  intro p hp hn
  have hp0 : p ≠ 0 := by intro h; simp [h] at hn
  have heq : normalized p = p := by simp [normalized, hn]
  have hh := normalized_inner_le_planeError P z hp hp0
  rw [heq] at hh
  exact hh.trans hr.le

/-- The error values of all nontrivial chords in a candidate leaf. -/
def leafErrorValues (C : Set E) (ds : ℕ) (Γ : Set E) : Set ℝ :=
  {r | ∃ x ∈ Γ, ∃ y ∈ Γ, x ≠ y ∧ r = normalError C ds (y - x)}

/-- The literal outer supremum in the fake-leaf condition. -/
def leafError (C : Set E) (ds : ℕ) (Γ : Set E) : ℝ := sSup (leafErrorValues C ds Γ)

theorem leafErrorValues_le_one {C : Set E} {ds : ℕ} (hds : 0 < ds)
    (hplanes : (admissiblePlanes C ds).Nonempty) (Γ : Set E) :
    ∀ r ∈ leafErrorValues C ds Γ, r ≤ 1 := by
  rintro r ⟨x, _, y, _, _, rfl⟩
  exact normalError_le_one hds hplanes (y - x)

theorem leafErrorValues_bddAbove {C : Set E} {ds : ℕ} (hds : 0 < ds)
    (hplanes : (admissiblePlanes C ds).Nonempty) (Γ : Set E) :
    BddAbove (leafErrorValues C ds Γ) := ⟨1, leafErrorValues_le_one hds hplanes Γ⟩

/-- Outer supremum zero makes every nontrivial chord's literal inner infimum zero. -/
theorem normalError_eq_zero_of_leafError_zero {C : Set E} {ds : ℕ} (hds : 0 < ds)
    (hplanes : (admissiblePlanes C ds).Nonempty) {Γ : Set E}
    (hzero : leafError C ds Γ = 0) {x y : E} (hx : x ∈ Γ) (hy : y ∈ Γ) (hxy : x ≠ y) :
    normalError C ds (y - x) = 0 := by
  apply le_antisymm
  · have hh := le_csSup (leafErrorValues_bddAbove hds hplanes Γ)
      (show normalError C ds (y - x) ∈ leafErrorValues C ds Γ from ⟨x, hx, y, hy, hxy, rfl⟩)
    exact hh.trans_eq hzero
  · exact normalError_nonneg hds hplanes _

/-- Uniform secant bounds are derived from the literal fake-leaf formula. -/
theorem exists_uniform_fakeLeaf_slope (U : Submodule ℝ E) {C : Set E}
    (hclosed : IsClosed C)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (htrans : ∀ v ∈ C, v ∈ U → v = 0)
    (hds : 0 < Module.finrank ℝ Uᗮ)
    (hplanes : (admissiblePlanes C (Module.finrank ℝ Uᗮ)).Nonempty) :
    ∃ L : ℝ, 0 < L ∧ ∀ Γ : Set E,
      leafError C (Module.finrank ℝ Uᗮ) Γ = 0 →
      ∀ x ∈ Γ, ∀ y ∈ Γ, ‖Uᗮ.starProjection (x - y)‖ ≤ L * ‖U.starProjection (x - y)‖ := by
  obtain ⟨L, hL, hb⟩ := ConeGraphGeometry.exists_uniform_approximate_secant_slope
    U hclosed hscale htrans
  refine ⟨L, hL, fun Γ hΓ x hx y hy => ?_⟩
  by_cases hxy : x = y
  · simp [hxy]
  have hz := normalError_eq_zero_of_leafError_zero hds hplanes hΓ hy hx (Ne.symm hxy)
  apply hb (x - y)
  intro ε hε
  exact exists_approximate_normal_plane hplanes (x - y) hz hε

/-- The manuscript condition gives a uniformly controlled, injective unstable
projection on every candidate fake leaf, without assuming a graph description. -/
theorem exists_uniform_fakeLeaf_projection (U : Submodule ℝ E) {C : Set E}
    (hclosed : IsClosed C)
    (hscale : ∀ r : ℝ, 0 ≤ r → ∀ v ∈ C, r • v ∈ C)
    (htrans : ∀ v ∈ C, v ∈ U → v = 0)
    (hds : 0 < Module.finrank ℝ Uᗮ)
    (hplanes : (admissiblePlanes C (Module.finrank ℝ Uᗮ)).Nonempty) :
    ∃ L : ℝ, 0 < L ∧ ∀ Γ : Set E,
      leafError C (Module.finrank ℝ Uᗮ) Γ = 0 →
      AntilipschitzWith (Real.toNNReal (1 + L))
        (fun x : Γ => U.orthogonalProjectionOnto (x : E)) := by
  obtain ⟨L, hL, hb⟩ := exists_uniform_fakeLeaf_slope U hclosed hscale htrans hds hplanes
  exact ⟨L, hL, fun Γ hΓ => ConeGraphGeometry.leafProjection_antilipschitz U hL.le (hb Γ hΓ)⟩

end LeanShared.FakeLeafGeometry
