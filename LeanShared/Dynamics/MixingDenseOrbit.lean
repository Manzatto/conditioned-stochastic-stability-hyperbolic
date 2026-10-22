module

public import LeanShared.Dynamics.DenseOrbitFromHitting
public import LeanShared.Dynamics.ProductIsolationMixing

/-! Compact second-countable mixing cores have a literal dense integer orbit.
This supplies the product basic-set witness without adding it as an input. -/

public noncomputable section
open Set Function
namespace LeanShared.HyperbolicBasicSet
variable {M : Type*} [MetricSpace M] [SecondCountableTopology M]

 theorem MixingOn.exists_dense_orbit {T : M ≃ₜ M} {K : Set M}
    (mixing : MixingOn T K) (compact : IsCompact K) (nonempty : K.Nonempty)
    (invariant : T '' K = K) :
    ∃ x ∈ K, K ⊆ closure (range (orbit T x)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp compact
  let : Nonempty K := nonempty.to_subtype
  have maps : MapsTo T K K := fun x hx => invariant ▸ mem_image_of_mem T hx
  let f : K → K := fun x => ⟨T x, maps x.property⟩
  have continuous : Continuous f := (T.continuous.comp continuous_subtype_val).subtype_mk _
  have iterate (n : ℕ) (x : K) : (f^[n] x).val = (T : M → M)^[n] x.val := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [iterate_succ_apply', f, ih]
  have hitting (U V : Set K) (openU : IsOpen U) (openV : IsOpen V)
      (nonemptyU : U.Nonempty) (nonemptyV : V.Nonempty) :
      ∃ n : ℕ, ∃ x ∈ U, f^[n] x ∈ V := by
    obtain ⟨U0, openU0, rfl⟩ := isOpen_induced_iff.mp openU
    obtain ⟨V0, openV0, rfl⟩ := isOpen_induced_iff.mp openV
    obtain ⟨x, hx⟩ := nonemptyU
    obtain ⟨y, hy⟩ := nonemptyV
    obtain ⟨N, hits⟩ := mixing U0 V0 openU0 openV0
      ⟨x.val, x.property, hx⟩ ⟨y.val, y.property, hy⟩
    obtain ⟨z, ⟨inK, inU⟩, inV⟩ := hits N le_rfl
    refine ⟨N, ⟨z, inK⟩, inU, ?_⟩
    change (f^[N] ⟨z, inK⟩).val ∈ V0
    simpa only [iterate] using inV
  obtain ⟨x, dense⟩ := exists_dense_forward_orbit f continuous hitting
  refine ⟨x.val, x.property, ?_⟩
  intro p hp
  apply mem_closure_iff.mpr
  intro U openU inU
  obtain ⟨z, zU, hz⟩ := dense_iff_inter_open.mp dense
    (Subtype.val ⁻¹' U) (openU.preimage continuous_subtype_val) ⟨⟨p, hp⟩, inU⟩
  obtain ⟨n, rfl⟩ := hz
  refine ⟨(T : M → M)^[n] x.val, ?_, ?_⟩
  · simpa only [Set.mem_preimage, iterate] using zU
  · refine ⟨(n : ℤ), ?_⟩
    simp only [orbit, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]

/-- The product orbit witness follows from mixing of both original cores. -/
theorem MixingOn.exists_product_dense_orbit {N : Type*} [MetricSpace N]
    [SecondCountableTopology N] {T : M ≃ₜ M} {S : N ≃ₜ N} {K : Set M} {L : Set N}
    (mixingT : MixingOn T K) (mixingS : MixingOn S L)
    (compactK : IsCompact K) (compactL : IsCompact L)
    (nonemptyK : K.Nonempty) (nonemptyL : L.Nonempty)
    (invariantK : T '' K = K) (invariantL : S '' L = L) :
    ∃ z ∈ K ×ˢ L, K ×ˢ L ⊆ closure (range (orbit (T.prodCongr S) z)) := by
  apply (mixingT.product mixingS).exists_dense_orbit
    (compactK.prod compactL) (nonemptyK.prod nonemptyL)
  change (fun p : M × N => (T p.1, S p.2)) '' (K ×ˢ L) = K ×ˢ L
  rw [← Set.prod_image_image_eq, invariantK, invariantL]

end LeanShared.HyperbolicBasicSet
