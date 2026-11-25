module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.SpanSingletonProduct
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.RingKrullDimQuotientSpanSingletonAddOne
public import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace IsRegularLocalRing

open IsLocalRing
open PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing
  (spanFinrank_maximalIdeal_quotient_succ_le spanFinrank_quotient_eq_and_ringKrullDim_add_one)

universe u

private theorem isLocalRing_quotient_span_singleton {R : Type*} [CommRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have hIle : Ideal.span ({x} : Set R) ≤ maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  have hIne : Ideal.span ({x} : Set R) ≠ ⊤ := by
    intro h
    rw [h, top_le_iff] at hIle
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top hIle
  have hone : (1 : R ⧸ Ideal.span ({x} : Set R)) ≠ 0 := by
    intro h
    have h1 : (1 : R) ∈ Ideal.span ({x} : Set R) := by
      rwa [← Ideal.Quotient.eq_zero_iff_mem, map_one]
    exact hIne ((Ideal.eq_top_iff_one _).mpr h1)
  have : Nontrivial (R ⧸ Ideal.span ({x} : Set R)) := ⟨⟨1, 0, hone⟩⟩
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

private theorem isPrime_of_mem_minimalPrimes {R : Type*} [CommRing R] {p : Ideal R}
    (hp : p ∈ minimalPrimes R) : p.IsPrime := hp.1.1

private theorem le_of_le_of_mem_minimalPrimes {R : Type*} [CommRing R] {p q : Ideal R}
    (hp : p ∈ minimalPrimes R) (hq : q.IsPrime) (hle : q ≤ p) : p ≤ q :=
  hp.2 ⟨hq, bot_le⟩ hle

private theorem isDomain_of_maximalIdeal_eq_bot (R : Type*) [CommRing R] [IsLocalRing R]
    (h : maximalIdeal R = ⊥) : IsDomain R := by
  have hp : (maximalIdeal R).IsPrime := (maximalIdeal.isMaximal R).isPrime
  rw [h] at hp
  have := hp
  exact IsDomain.of_bot_isPrime R

private theorem maximalIdeal_eq_bot_of_le_sq (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (h : maximalIdeal R ≤ maximalIdeal R ^ 2) : maximalIdeal R = ⊥ := by
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
    (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  show maximalIdeal R ≤ maximalIdeal R * maximalIdeal R
  rw [← pow_two]
  exact h

private theorem exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes (R : Type*) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (hsq : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2)
    (hmin : ¬ ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p) :
    ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  obtain ⟨t, ht⟩ := (minimalPrimes.finite_of_isNoetherianRing R).exists_finset_coe
  by_contra hcon
  push Not at hcon
  have hsub : (maximalIdeal R : Set R) ⊆
      ⋃ i ∈ ((insert (maximalIdeal R ^ 2) t : Finset (Ideal R)) : Set (Ideal R)), (i : Set R) := by
    intro y hy
    rcases em (y ∈ maximalIdeal R ^ 2) with hm2 | hm2
    · exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)) hm2
    · obtain ⟨p, hp, hyp⟩ := hcon y hy hm2
      have hpt : p ∈ insert (maximalIdeal R ^ 2) t := by
        apply Finset.mem_insert_of_mem
        rw [← Finset.mem_coe, ht]
        exact hp
      exact Set.mem_biUnion (Finset.mem_coe.mpr hpt) hyp
  have hp : ∀ i ∈ (insert (maximalIdeal R ^ 2) t : Finset (Ideal R)),
      i ≠ maximalIdeal R ^ 2 → i ≠ maximalIdeal R ^ 2 → i.IsPrime := by
    intro i hi h1 _
    have hit : i ∈ t := by
      rcases Finset.mem_insert.mp hi with hh | hh
      · exact absurd hh h1
      · exact hh
    refine isPrime_of_mem_minimalPrimes ?_
    rw [← ht]
    exact Finset.mem_coe.mpr hit
  obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime _ _ hp).mp hsub
  rcases Finset.mem_insert.mp hi with hh | hh
  · subst hh
    exact hsq hle
  · refine hmin ⟨i, ?_, hle⟩
    rw [← ht]
    exact Finset.mem_coe.mpr hh

theorem isRegularLocalRing_quotient_span_singleton {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have := isLocalRing_quotient_span_singleton hx
  rw [isRegularLocalRing_iff]
  exact_mod_cast (spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2).1

theorem ringKrullDim_quotient_span_singleton_add_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have := isLocalRing_quotient_span_singleton hx
  exact (spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2).2

private theorem isDomain_of_forall_spanFinrank_lt (R : Type u) [CommRing R]
    [IsRegularLocalRing R]
    (IH : ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      Submodule.spanFinrank (maximalIdeal S) < Submodule.spanFinrank (maximalIdeal R) →
        IsDomain S) :
    IsDomain R := by
  classical
  by_cases hsq : maximalIdeal R ≤ maximalIdeal R ^ 2
  · exact isDomain_of_maximalIdeal_eq_bot R (maximalIdeal_eq_bot_of_le_sq R hsq)
  by_cases hmin : ∃ p ∈ minimalPrimes R, maximalIdeal R ≤ p
  · exfalso
    obtain ⟨p, hp, hple⟩ := hmin
    have hpp : p.IsPrime := isPrime_of_mem_minimalPrimes hp
    have hpm : p = maximalIdeal R := le_antisymm (IsLocalRing.le_maximalIdeal hpp.ne_top) hple
    have hallideal : ∀ q : Ideal R, q.IsPrime → q = maximalIdeal R := by
      intro q hq
      refine le_antisymm (IsLocalRing.le_maximalIdeal hq.ne_top) ?_
      rw [← hpm]
      exact le_of_le_of_mem_minimalPrimes hp hq
        (by rw [hpm]; exact IsLocalRing.le_maximalIdeal hq.ne_top)
    have h2 : ringKrullDim R ≤ 0 := by
      have hPQ : ∀ P Q : PrimeSpectrum R, P = Q := by
        intro P Q
        apply PrimeSpectrum.ext
        rw [hallideal P.asIdeal P.isPrime, hallideal Q.asIdeal Q.isPrime]
      have : Subsingleton (PrimeSpectrum R) := ⟨hPQ⟩
      exact Order.krullDim_nonpos_of_subsingleton
    obtain ⟨x, hx, hx2⟩ : ∃ x, x ∈ maximalIdeal R ∧ x ∉ maximalIdeal R ^ 2 := by
      by_contra hc
      push Not at hc
      exact hsq fun y hy => hc y hy
    have := isLocalRing_quotient_span_singleton hx
    have hpos := spanFinrank_maximalIdeal_quotient_succ_le R hx hx2
    have hdim : ringKrullDim R =
        (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) :=
      ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance).symm
    rw [hdim] at h2
    have hle0 : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 0 := by exact_mod_cast h2
    omega
  · obtain ⟨x, hx, hx2, hxp⟩ :=
      exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes R hsq hmin
    have := isLocalRing_quotient_span_singleton hx
    have hrq : IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) :=
      isRegularLocalRing_quotient_span_singleton hx hx2
    have hlt : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span ({x} : Set R))) <
        Submodule.spanFinrank (maximalIdeal R) := by
      have h1 := spanFinrank_maximalIdeal_quotient_succ_le R hx hx2
      have h2 : Submodule.spanFinrank (maximalIdeal R)
          = Module.finrank (ResidueField R) (CotangentSpace R) := by
        rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
      omega
    have hdom := IH (R ⧸ Ideal.span ({x} : Set R)) hlt
    have hprime : (Ideal.span ({x} : Set R)).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp hdom
    obtain ⟨p, hp, hple⟩ :=
      Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ Ideal.span ({x} : Set R))
    have hpp : p.IsPrime := isPrime_of_mem_minimalPrimes hp
    have hpbot : p = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p
        (IsNoetherian.noetherian p) ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
      intro y hy
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp (hple hy)
      have ha : a ∈ p := by
        rcases hpp.mem_or_mem hy with hh | hh
        · exact absurd hh (hxp p hp)
        · exact hh
      exact Ideal.mul_mem_mul hx ha
    rw [hpbot] at hpp
    have := hpp
    exact IsDomain.of_bot_isPrime R

private theorem isDomain_of_spanFinrank_le :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      Submodule.spanFinrank (maximalIdeal R) ≤ n → IsDomain R := by
  intro n
  induction n with
  | zero =>
    intro R _ _ h
    refine isDomain_of_forall_spanFinrank_lt R ?_
    intro S _ _ hS
    exact absurd (lt_of_lt_of_le hS h) (Nat.not_lt_zero _)
  | succ n IH =>
    intro R _ _ h
    refine isDomain_of_forall_spanFinrank_lt R ?_
    intro S _ _ hS
    exact IH S (by omega)

theorem isDomain (R : Type*) [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_spanFinrank_le (Submodule.spanFinrank (IsLocalRing.maximalIdeal R)) R le_rfl

instance (priority := 100) instIsDomain {R : Type*} [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain R

private theorem false_of_eq_smul_of_linearIndependent {K M : Type*} {ι : Type*} [Field K]
    [AddCommGroup M] [Module K M] {v : ι → M} (h : LinearIndependent K v) {i j : ι}
    (hij : i ≠ j) (c : K) (he : v j = c • v i) : False := by
  classical
  have key : ∑ k ∈ ({i, j} : Finset ι),
      (fun k => if k = i then c else if k = j then (-1 : K) else 0) k • v k = 0 := by
    rw [Finset.sum_pair hij]
    simp [Ne.symm hij, he]
  have h2 := linearIndependent_iff'.mp h {i, j}
      (fun k => if k = i then c else if k = j then (-1 : K) else 0) key j (by simp)
  simp [Ne.symm hij] at h2

private theorem toCotangent_mul_eq_smul {R : Type*} [CommRing R] [IsLocalRing R] (r a : R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) (hra : r * a ∈ IsLocalRing.maximalIdeal R) :
    ((IsLocalRing.maximalIdeal R).toCotangent ⟨r * a, hra⟩ : IsLocalRing.CotangentSpace R) =
      algebraMap R (IsLocalRing.ResidueField R) r •
        ((IsLocalRing.maximalIdeal R).toCotangent ⟨a, ha⟩ : IsLocalRing.CotangentSpace R) := by
  have h1 : (⟨r * a, hra⟩ : IsLocalRing.maximalIdeal R)
      = r • (⟨a, ha⟩ : IsLocalRing.maximalIdeal R) := Subtype.ext rfl
  rw [algebraMap_smul, h1, map_smul]

theorem notMem_maximalIdeal_sq {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R))
    (i : ι) : x i ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  intro hmem
  have h0 : ((IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
      IsLocalRing.CotangentSpace R) = 0 := by
    rw [Ideal.toCotangent_eq_zero]
    exact hmem
  exact hli.ne_zero i h0

theorem isPrime_span_singleton {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R))
    (i : ι) : (Ideal.span ({x i} : Set R)).IsPrime := by
  have : IsRegularLocalRing (R ⧸ Ideal.span ({x i} : Set R)) :=
    isRegularLocalRing_quotient_span_singleton (hx i) (notMem_maximalIdeal_sq x hx hli i)
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact IsRegularLocalRing.isDomain _

theorem notMem_span_singleton {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R))
    {i j : ι} (hij : i ≠ j) : x j ∉ Ideal.span ({x i} : Set R) := by
  intro hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  have hmem2 : r * x i ∈ IsLocalRing.maximalIdeal R := by
    rw [hr]
    exact hx j
  have key : ((IsLocalRing.maximalIdeal R).toCotangent ⟨x j, hx j⟩ :
      IsLocalRing.CotangentSpace R)
      = algebraMap R (IsLocalRing.ResidueField R) r •
        ((IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
          IsLocalRing.CotangentSpace R) := by
    have hsub : (⟨x j, hx j⟩ : IsLocalRing.maximalIdeal R) = ⟨r * x i, hmem2⟩ :=
      Subtype.ext hr.symm
    rw [hsub]
    exact toCotangent_mul_eq_smul r (x i) (hx i) hmem2
  exact false_of_eq_smul_of_linearIndependent hli hij _ key

theorem isRadical_span_singleton_prod {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    [Fintype ι] (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R)) :
    (Ideal.span ({∏ i, x i} : Set R)).IsRadical := by
  classical
  exact FunctorialResolution.EmbeddedResolution.isRadical_span_singleton_prod_finset x Finset.univ
    (fun i _ => isPrime_span_singleton x hx hli i)
    (fun i _ j _ hij => notMem_span_singleton x hx hli hij)

end IsRegularLocalRing
