module
public import LeanShared.Dynamics.MixingDenseOrbit
public import LeanShared.Dynamics.BilateralHomeomorphismOrbit
public import Mathlib.Dynamics.PeriodicPts.Defs

/-! A core with a dense integer orbit and dense periodic points is
forward transitive at arbitrarily late times. Its product with a mixing
core therefore has a dense orbit, even if the first core is not mixing. -/
public noncomputable section
open Set Function
namespace LeanShared.HyperbolicBasicSet
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem orbit_eq_zpow (T:X≃ₜX) (x:X) (k:ℤ) : orbit T x k=(T^k) x := by
  unfold orbit
  split_ifs with h
  · rw [← Int.toNat_of_nonneg h,zpow_natCast]
    exact (congrFun (DiffeomorphismIterates.coe_pow T k.toNat) x).symm
  · have positive : 0≤-k := by omega
    have negative : k = -(((-k).toNat : ℕ):ℤ) := by rw [Int.toNat_of_nonneg positive]; omega
    rw [negative,zpow_neg,zpow_natCast]
    simpa only [neg_neg,Int.toNat_natCast,Homeomorph.inv_apply] using
      (congrFun (DiffeomorphismIterates.coe_symm_pow T (-k).toNat) x).symm

theorem periodic_late_forward (T:X≃ₜX) {p:X} (periodic:p∈periodicPts (T:X→X))
    (k:ℤ) (N:ℕ) : ∃ n:ℕ, N≤n ∧ (T:X→X)^[n] p=(T^k) p := by
  obtain ⟨q,posQ,returns⟩ := periodic
  obtain ⟨m,rfl|rfl⟩ := Int.eq_nat_or_neg k
  · refine ⟨m+q*N,?_,?_⟩
    · exact (Nat.le_mul_of_pos_left N posQ).trans (Nat.le_add_left _ _)
    · rw [iterate_add_apply,(returns.mul_const N).eq,zpow_natCast]
      exact (congrFun (DiffeomorphismIterates.coe_pow T m) p).symm
  · let n := q*(N+m)-m
    have enough : N+m≤q*(N+m) := Nat.le_mul_of_pos_left (N+m) posQ
    refine ⟨n,by dsimp [n]; omega,?_⟩
    rw [zpow_neg,zpow_natCast]
    have target := congrFun (DiffeomorphismIterates.coe_symm_pow T m) p
    change (T:X→X)^[n] p=(T^m).symm p
    rw [target]
    apply T.injective.iterate m
    rw [← iterate_add_apply]
    have total : m+n=q*(N+m) := by dsimp [n]; omega
    rw [total,(returns.mul_const (N+m)).eq]
    exact (T.right_inv.iterate m p).symm

theorem late_hitting_of_dense_integer_orbit (T:X≃ₜX) (K:Set X)
    (invariant:T '' K=K)
    (denseOrbit:∃x∈K,K⊆closure (range (orbit T x)))
    (densePeriodic:K⊆closure (K∩periodicPts (T:X→X)))
    (U W:Set X) (openU:IsOpen U) (openW:IsOpen W)
    (nonemptyU:(K∩U).Nonempty) (nonemptyW:(K∩W).Nonempty) (N:ℕ) :
    ∃n:ℕ,N≤n ∧ ∃p∈K∩U,(T:X→X)^[n] p∈W := by
  obtain ⟨x,hx,dense⟩ := denseOrbit
  obtain ⟨u,huK,huU⟩ := nonemptyU
  obtain ⟨v,hvK,hvW⟩ := nonemptyW
  obtain ⟨u',hu'U,⟨m,rfl⟩⟩ := mem_closure_iff.mp (dense huK) U openU huU
  obtain ⟨v',hv'W,⟨n,rfl⟩⟩ := mem_closure_iff.mp (dense hvK) W openW hvW
  have maps : MapsTo T K K := fun y hy=>invariant ▸ mem_image_of_mem T hy
  have inverse : MapsTo T.symm K K := by
    intro y hy
    rw [←invariant] at hy
    obtain ⟨z,hz,rfl⟩ := hy
    simpa using hz
  have orbitK : orbit T x m∈K := by
    unfold orbit
    split_ifs
    · exact maps.iterate _ hx
    · exact inverse.iterate _ hx
  have hits : (T^(n-m)) (orbit T x m)=orbit T x n := by
    rw [orbit_eq_zpow,orbit_eq_zpow]
    change ((T^(n-m))*(T^m)) x=(T^n) x
    rw [← zpow_add,sub_add_cancel]
  let O := U∩(T^(n-m)) ⁻¹' W
  have openO : IsOpen O := openU.inter (openW.preimage (T^(n-m)).continuous)
  have inO : orbit T x m∈O := ⟨hu'U,by change (T^(n-m)) (orbit T x m)∈W; rw [hits]; exact hv'W⟩
  obtain ⟨p,hpO,hp⟩ := mem_closure_iff.mp (densePeriodic orbitK) O openO inO
  obtain ⟨r,late,hr⟩ := periodic_late_forward T hp.2 (n-m) N
  exact ⟨r,late,p,⟨hp.1,hpO.1⟩,hr ▸ hpO.2⟩

/-- A mixing auxiliary synchronizes with arbitrarily late original hits. -/
theorem product_hitting_of_late_hitting {T:X≃ₜX} {S:Y≃ₜY} {K:Set X} {L:Set Y}
    (late:∀U W:Set X,IsOpen U→IsOpen W→(K∩U).Nonempty→(K∩W).Nonempty→
      ∀N:ℕ,∃n:ℕ,N≤n ∧ ∃p∈K∩U,(T:X→X)^[n] p∈W)
    (mixing:MixingOn S L) :
    ∀U W:Set (X×Y),IsOpen U→IsOpen W→((K×ˢL)∩U).Nonempty→((K×ˢL)∩W).Nonempty→
      ∃n:ℕ,∃p∈(K×ˢL)∩U,(T.prodCongr S:X×Y→X×Y)^[n] p∈W := by
  intro U W openU openW nonemptyU nonemptyW
  obtain ⟨⟨x,y⟩,⟨⟨hxK,hyL⟩,hxyU⟩⟩ := nonemptyU
  obtain ⟨⟨a,b⟩,⟨⟨haK,hbL⟩,habW⟩⟩ := nonemptyW
  obtain ⟨UX,UY,hUX,hUY,hxU,hyU,hprodU⟩ := isOpen_prod_iff.mp openU x y hxyU
  obtain ⟨WX,WY,hWX,hWY,haW,hbW,hprodW⟩ := isOpen_prod_iff.mp openW a b habW
  obtain ⟨N,hN⟩ := mixing UY WY hUY hWY ⟨y,hyL,hyU⟩ ⟨b,hbL,hbW⟩
  obtain ⟨n,hn,v,hv,hvW⟩ := late UX WX hUX hWX ⟨x,hxK,hxU⟩ ⟨a,haK,haW⟩ N
  obtain ⟨w,hw,hwW⟩ := hN n hn
  refine ⟨n,(v,w),⟨⟨hv.1,hw.1⟩,hprodU ⟨hv.2,hw.2⟩⟩,?_⟩
  change (Prod.map T S)^[n] (v,w)∈W
  rw [iterate_independent]
  exact hprodW ⟨hvW,hwW⟩

theorem exists_dense_orbit_of_hitting {M:Type*} [MetricSpace M] [SecondCountableTopology M]
    {T : M ≃ₜ M} {K : Set M}
    (hits : ∀ U V : Set M,IsOpen U→IsOpen V→(K∩U).Nonempty→(K∩V).Nonempty→
      ∃ n:ℕ,∃ x∈K∩U,(T:M→M)^[n] x∈V) (compact : IsCompact K) (nonempty : K.Nonempty)
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
    obtain ⟨N,z,⟨inK,inU⟩,inV⟩ := hits U0 V0 openU0 openV0
      ⟨x.val,x.property,hx⟩ ⟨y.val,y.property,hy⟩
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


theorem exists_product_dense_orbit_of_periodic_dense
    [SecondCountableTopology X] [SecondCountableTopology Y]
    {T:X≃ₜX} {S:Y≃ₜY} {K:Set X} {L:Set Y}
    (compactK:IsCompact K) (compactL:IsCompact L)
    (nonemptyK:K.Nonempty) (nonemptyL:L.Nonempty)
    (invariantK:T '' K=K) (invariantL:S '' L=L)
    (denseOrbit:∃x∈K,K⊆closure (range (orbit T x)))
    (densePeriodic:K⊆closure (K∩periodicPts (T:X→X)))
    (mixing:MixingOn S L) :
    ∃z∈K×ˢL,K×ˢL⊆closure (range (orbit (T.prodCongr S) z)) := by
  apply exists_dense_orbit_of_hitting
    (product_hitting_of_late_hitting
      (late_hitting_of_dense_integer_orbit T K invariantK denseOrbit densePeriodic) mixing)
    (compactK.prod compactL) (nonemptyK.prod nonemptyL)
  change (Prod.map T S) '' (K×ˢL)=K×ˢL
  rw [prodMap_image_prod,invariantK,invariantL]

end LeanShared.HyperbolicBasicSet
