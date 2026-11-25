module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem exists_fin_min {σ : Type} [Fintype σ] (P : (σ →₀ ℕ) → Prop) :
    ∃ T : Finset (σ →₀ ℕ), (∀ m ∈ T, P m) ∧ ∀ n, P n → ∃ m ∈ T, m ≤ n := by
  classical
  have hfin : {m : σ →₀ ℕ | Minimal P m}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)
  refine ⟨hfin.toFinset, fun m hm => ((Set.Finite.mem_toFinset hfin).1 hm).1, ?_⟩
  intro n hn
  obtain ⟨b, hb, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE {x | P x}).exists_le_minimal hn
  exact ⟨b, (Set.Finite.mem_toFinset hfin).2 hmin, hb⟩

private theorem exists_decomp {O σ X : Type} [CommRing O] [Fintype σ] [AddCommGroup X] (wt : σ → X) (j : X)
    (f : MvPowerSeries σ O) (hf : f ∈ wtPart O wt j) :
    ∃ (T : Finset (σ →₀ ℕ)) (g : (σ →₀ ℕ) → MvPowerSeries σ O), (∀ m ∈ T, g m ∈ wtPart O wt 0) ∧
      f = ∑ m ∈ T, monomial m (1 : O) * g m := by
  classical
  obtain ⟨T, hTP, hT⟩ := exists_fin_min (fun n => coeff n f ≠ 0)
  choose! c hcT hcle using hT
  obtain ⟨g, hg⟩ : ∃ g : (σ →₀ ℕ) → MvPowerSeries σ O, ∀ m k,
      coeff k (g m) = if coeff (k + m) f ≠ 0 ∧ c (k + m) = m then coeff (k + m) f else 0 :=
    ⟨fun m k => if coeff (k + m) f ≠ 0 ∧ c (k + m) = m then coeff (k + m) f else 0, fun _ _ => rfl⟩
  have hwt : ∀ n, coeff n f ≠ 0 → Finsupp.weight wt n = j := by
    intro n hn
    by_contra h
    exact hn (hf n h)
  refine ⟨T, g, ?_, ?_⟩
  · intro m hmT k hk
    rw [hg, ite_eq_right]
    rintro ⟨h1, h2⟩
    apply hk
    have hm : Finsupp.weight wt m = j := hwt m (hTP m hmT)
    have hkm := hwt _ h1
    rw [map_add (f := _), hm] at hkm
    simpa using hkm
  · ext n

    rw [map_sum, Finset.sum_congr rfl
    (g := fun m => if c n = m then (if coeff n f ≠ 0 then coeff n f else 0) else 0),
    Finset.sum_ite_eq]
    · by_cases hn : coeff n f ≠ 0
      · rw [ite_eq_left (hcT n hn), ite_eq_left hn]
      · push Not at hn
        rw [hn]
        simp
    · intro m _
      rw [MvPowerSeries.coeff_monomial_mul, one_mul]
      by_cases hmn : m ≤ n
      · rw [ite_eq_left hmn, hg, tsub_add_cancel_of_le hmn]
        by_cases h1 : coeff n f ≠ 0 <;> by_cases h2 : c n = m <;> simp [h1, h2]
      · rw [ite_eq_right hmn]
        by_cases h1 : coeff n f ≠ 0
        · have h3 : c n ≠ m := fun h => hmn (h ▸ hcle n h1)
          simp [h3]
        · push Not at h1
          simp [h1]

theorem UpperTheory.V.Alg.gr_gen :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (W : WPres O X R), Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) = ⊤ := by
  intro O R _ _ _ X _ _ _ W
  classical
  haveI := W.fin
  rw [Algebra.eq_top_iff]
  rintro ⟨x, hx⟩
  refine Submodule.iSup_induction' (p := W.part)
    (motive := fun x h => (⟨x, h⟩ : W.A) ∈ Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA))
    ?_ ?_ ?_ hx
  · intro j y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨T, g, hg, hfe⟩ := exists_decomp W.wt j f hf
    have hg' : ∀ m, (if m ∈ T then g m else 0) ∈ wtPart O W.wt 0 := by
      intro m
      split_ifs with h
      · exact hg m h
      · exact zero_mem _
    let e : (W.σ →₀ ℕ) → W.A := fun m =>
      ⟨W.π (if m ∈ T then g m else 0), W.part_le_A (Submodule.mem_map_of_mem (hg' m))⟩
    have he : ∀ m, e m ∈ W.gr 0 := fun m => Submodule.mem_map_of_mem (hg' m)
    have hmem : (∑ m ∈ T, (∏ i, W.zA i ^ m i) * e m) ∈
        Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) := by
      refine Subalgebra.sum_mem _ fun m _ => Subalgebra.mul_mem _ ?_ ?_
      · refine Subalgebra.prod_mem _ fun i _ => pow_mem ?_ _
        exact Algebra.subset_adjoin (Set.mem_union_right _ ⟨i, rfl⟩)
      · exact Algebra.subset_adjoin (Set.mem_union_left _ (he m))
    convert hmem using 1
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_finsetProd,
      SubmonoidClass.coe_pow, e, WPres.zA, WPres.z]

    rw [AlgHom.toLinearMap_apply, hfe, map_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [ite_eq_left hm, map_mul, MvPowerSeries.monomial_one_eq,
      Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (fun _ _ => pow_zero _),
      map_prod]
    simp only [map_pow]
  · exact Subalgebra.zero_mem _
  · intro x y _ _ ihx ihy
    exact Subalgebra.add_mem _ ihx ihy
