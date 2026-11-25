module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftSpread
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartLatQCech
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.SimpleRing.Principal

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpreadRead, GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpread

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpreadRead =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpreadRead", "h": "module\n\nimport GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartLatQCech\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Ring.IsFormallyReal\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenRead

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω}

private def evLHom {T : Submonoid (MRingOver ℚ ι)} (hT : ∀ t ∈ T, aeval y t ≠ 0) :
    LocalizedModule T (MRingOver ℚ ι ⧸ GenOnFibres.idealOver y ℚ) →+* Ω where
  toFun := ChartLatQCech.val y T
  map_one' := by
    rw [show (1 : LocalizedModule T (MRingOver ℚ ι ⧸ GenOnFibres.idealOver y ℚ)) =
      LocalizedModule.mk 1 1 by rw [OreLocalization.one_def], ChartLatQCech.val_mk hT]
    simp
  map_mul' x x' := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
    induction x' using LocalizedModule.induction_on with
    | h m' s' =>
    rw [LocalizedModule.mk_mul_mk, ChartLatQCech.val_mk hT, ChartLatQCech.val_mk hT,
      ChartLatQCech.val_mk hT]
    simp only [Submonoid.coe_mul, map_mul]
    field_simp [hT s s.2, hT s' s'.2]
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, ChartLatQCech.val_mk hT]
    simp
  map_add' := ChartLatQCech.val_add T

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

variable (y) in
theorem exists_sections_of_generatedV {n : K → ℤ} (hg : KH.GeneratedV ℚ (KH.genIdeal y) n) :
    ∃ (σ : Type) (_ : Fintype σ) (s : σ → Ω), (∀ j, s j ∈ chartLatQ y n 1) ∧
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ v : σ → Ω, (∀ j, v j ∈ chartRingQ y c) ∧
        ∑ j, v j * (s j * ∏ k, y ⟨k, c k⟩ ^ (-n k)) = 1 := by
  classical
  choose r z u hz hu hsum using hg
  have hcoc : ∀ I j, KH.cechD ℚ ι (MRingOver ℚ ι ⧸ KH.genIdeal y) 0 (z I j) = 0 := fun I j => by
    have h := (Submodule.mem_inf.mp (hz I j)).2
    rw [Submodule.restrictScalars_mem, LinearMap.mem_ker] at h
    exact h
  have hloc : ∀ I j (J : KH.Cell K ι 0),
      z I j J ∈ KH.locPart ι (KH.quotPart ℚ (KH.genIdeal y)) (KH.cellMon ℚ J.1) n :=
    fun I j J => (Submodule.mem_inf.mp (hz I j)).1 J (Set.mem_univ _)
  refine ⟨Σ c : (∀ k, ι k), Fin (r (ZeroCocycleSection.chartCell c)), inferInstance,
    fun p => ChartLatQCech.val y _ (z (ZeroCocycleSection.chartCell p.1) p.2 (ZeroCocycleSection.chartCell p.1)),
    fun p => ?_, fun c hc => ?_⟩
  · obtain ⟨c', j⟩ := p
    intro c hc
    simp only [Nat.cast_one, one_mul]
    by_cases hc' : ∀ k, y ⟨k, c' k⟩ ≠ 0
    · rw [ChartLatQCech.val_chart_eq (hcoc _ j) hc' hc]
      exact ChartLatQCech.val_mul_mem_chartRingQ hc (hloc _ j _)
    · have hT : ¬ ∀ t ∈ KH.cellMon ℚ (ZeroCocycleSection.chartCell c').1, aeval y t ≠ 0 := by
        push Not at hc' ⊢
        obtain ⟨k, hk⟩ := hc'
        exact ⟨X ⟨k, c' k⟩, Submonoid.subset_closure ⟨k, c' k, Finset.mem_singleton_self _, rfl⟩,
          by rw [aeval_X, hk]⟩
      unfold ChartLatQCech.val
      rw [dite_eq_right hT, zero_mul]
      exact zero_mem _
  · have hT : ∀ t ∈ KH.cellMon ℚ (ZeroCocycleSection.chartCell c).1, aeval y t ≠ 0 :=
      ChartLatQCech.cellMon_aevalQ_ne (ZeroCocycleSection.chartCell_good hc)
    refine ⟨fun p => if p.1 = c then ChartLatQCech.val y _ (u (ZeroCocycleSection.chartCell p.1) p.2) *
        ∏ k, y ⟨k, c k⟩ ^ (n k) else 0, fun p => ?_, ?_⟩
    · obtain ⟨c', j⟩ := p
      by_cases h : c' = c
      · subst h
        simp only [ite_true]
        have := ChartLatQCech.val_mul_mem_chartRingQ hc (hu (ZeroCocycleSection.chartCell c') j)
        simpa only [Pi.neg_apply, neg_neg] using this
      · simp only [h, ite_false]
        exact zero_mem _
    · let f : LocalizedModule (KH.cellMon ℚ (ZeroCocycleSection.chartCell c).1)
          (MRingOver ℚ ι ⧸ KH.genIdeal y) →+* Ω := evLHom hT
      have e : ∀ j, (if c = c then ChartLatQCech.val y _ (u (ZeroCocycleSection.chartCell c) j) *
            ∏ k, y ⟨k, c k⟩ ^ (n k) else 0) *
          (ChartLatQCech.val y _ (z (ZeroCocycleSection.chartCell c) j (ZeroCocycleSection.chartCell c)) *
            ∏ k, y ⟨k, c k⟩ ^ (-n k)) =
          f (u (ZeroCocycleSection.chartCell c) j *
            z (ZeroCocycleSection.chartCell c) j (ZeroCocycleSection.chartCell c)) := by
        intro j
        rw [ite_eq_left rfl, map_mul]
        show ChartLatQCech.val y _ (u (ZeroCocycleSection.chartCell c) j) * (∏ k, y ⟨k, c k⟩ ^ n k) *
            (ChartLatQCech.val y _ (z (ZeroCocycleSection.chartCell c) j (ZeroCocycleSection.chartCell c)) *
              ∏ k, y ⟨k, c k⟩ ^ (-n k)) =
          ChartLatQCech.val y _ (u (ZeroCocycleSection.chartCell c) j) *
            ChartLatQCech.val y _ (z (ZeroCocycleSection.chartCell c) j (ZeroCocycleSection.chartCell c))
        have h1 := GenOnFibres.prod_zpow_neg_mul y c hc n
        linear_combination (ChartLatQCech.val y _ (u (ZeroCocycleSection.chartCell c) j) *
          ChartLatQCech.val y _ (z (ZeroCocycleSection.chartCell c) j (ZeroCocycleSection.chartCell c))) * h1
      rw [Fintype.sum_sigma, Finset.sum_eq_single c]
      · refine (Finset.sum_congr rfl fun j _ => e j).trans ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← map_sum, hsum, map_one]
      · intro c' _ hc'
        simp [hc']
      · intro h
        exact absurd (Finset.mem_univ c) h

end GenRead

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpreadRead =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpread =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpread", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftSpread\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator\npublic import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpreadRead\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace LiftSpread

theorem exists_common {α : Type} [Fintype α] (Q : α → ℕ → Prop) (hQ : ∀ a n k, Q a n → Q a (k * n))
    (h : ∀ a, ∃ n, 1 ≤ n ∧ Q a n) : ∃ n, 1 ≤ n ∧ ∀ a, Q a n := by
  classical
  choose N hN1 hN using h
  refine ⟨∏ a, N a, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => by
    have := hN1 a; omega), fun a => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ a)
  rw [hm, mul_comm]
  exact hQ a _ m (hN a)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [∀ k, Fintype (ι k)] in
theorem prod_zpow_nsmul (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (t : ℕ) (a : K → ℤ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(t • a) k) = ∏ _l : Fin t, ∏ k, y ⟨k, c k⟩ ^ (-a k) := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  simp only [Pi.smul_apply, nsmul_eq_mul]
  ring

theorem prod_mem_chartLat (y : (Σ k, ι k) → Ω) {σ : Type} (t : ℕ) (a : K → ℤ) (x : σ → Ω)
    (hx : ∀ j, x j ∈ chartLat y a 1) (f : Fin t → σ) : ∏ l, x (f l) ∈ chartLat y (t • a) 1 := by
  intro c hc
  have hW : ∀ j, x j * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ chartRingZ y c := fun j => by
    have h := hx j c hc
    simpa only [Nat.cast_one, one_mul] using h
  simp only [Nat.cast_one, one_mul]
  rw [prod_zpow_nsmul, ← Finset.prod_mul_distrib]
  exact Subalgebra.prod_mem _ fun l _ => hW (f l)

end LiftSpread

theorem LiftSpread.proof : LiftSpread.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D N _ hA
  classical
  obtain ⟨q, hq, hgen, -⟩ := hA
  obtain ⟨σ, _, s, hs, hrel⟩ := GenRead.exists_sections_of_generatedV (y := y) hgen

  obtain ⟨M, hM1, hM⟩ := LiftSpread.exists_common (fun j n => (n : Ω) * s j ∈ chartLat y (q • N) 1)
    (fun j n k h => by
      have e : ((k * n : ℕ) : Ω) * s j = k • ((n : Ω) * s j) := by
        rw [nsmul_eq_mul]; push_cast; ring
      rw [e]
      exact AddSubgroup.nsmul_mem _ h k)
    (fun j => ChartDenominator.proof K ι Ω y (q • N) 1 (s j) (hs j))

  have hrel' : ∀ c : ∀ k, ι k, ∃ v : σ → Ω, (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ j, v j ∈ chartRingQ y c) ∧
      ∑ j, v j * (s j * ∏ k, y ⟨k, c k⟩ ^ (-(q • N) k)) = 1 := fun c => by
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨v, hv⟩ := hrel c hc
      exact ⟨v, fun _ => hv⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose v hv using hrel'
  obtain ⟨Δ, hΔ1, hΔ⟩ := LiftSpread.exists_common (α := (∀ k, ι k) × σ)
    (fun p n => (∀ k, y ⟨k, p.1 k⟩ ≠ 0) → (n : Ω) * v p.1 p.2 ∈ chartRingZ y p.1)
    (fun p n k h hc => by
      rw [Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ k) (h hc))
    (fun p => by
      by_cases hc : ∀ k, y ⟨k, p.1 k⟩ ≠ 0
      · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_adjoin_int _ ((hv p.1 hc).1 p.2)
        exact ⟨n, hn, fun _ => h⟩
      · exact ⟨1, le_rfl, fun h => absurd h hc⟩)
  refine ⟨q, Δ * M, 0, hq, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), fun t _ => ?_⟩

  let e := Fintype.equivFin (Fin t → σ)
  refine ⟨Fintype.card (Fin t → σ), fun i => ∏ l, (M : Ω) * s (e.symm i l), fun i => ?_, fun c hc => ?_⟩
  · rw [mul_smul]
    exact LiftSpread.prod_mem_chartLat y t (q • N) _ hM (e.symm i)
  · refine ⟨t, fun i => ∏ l, (Δ : Ω) * v c (e.symm i l), fun i => ?_, ?_⟩
    · exact Subalgebra.prod_mem _ fun l _ => hΔ (c, e.symm i l) hc
    · set w := ∏ k, y ⟨k, c k⟩ ^ (-(q • N) k) with hw
      have hbase : ∑ j, (Δ : Ω) * v c j * ((M : Ω) * s j * w) = ((Δ * M : ℕ) : Ω) := by
        have h1 := (hv c hc).2
        calc ∑ j, (Δ : Ω) * v c j * ((M : Ω) * s j * w) = (Δ : Ω) * M * ∑ j, v c j * (s j * w) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by ring
          _ = ((Δ * M : ℕ) : Ω) := by rw [h1]; push_cast; ring
      rw [e.symm.sum_comp (fun f : Fin t → σ =>
        (∏ l, (Δ : Ω) * v c (f l)) * ((∏ l, (M : Ω) * s (f l)) *
          ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k)))]
      calc ∑ f : Fin t → σ, (∏ l, (Δ : Ω) * v c (f l)) * ((∏ l, (M : Ω) * s (f l)) *
            ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k))
          = ∑ f : Fin t → σ, ∏ l, ((Δ : Ω) * v c (f l) * ((M : Ω) * s (f l) * w)) := by
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [mul_smul, LiftSpread.prod_zpow_nsmul, ← hw, ← Finset.prod_mul_distrib,
              ← Finset.prod_mul_distrib]
        _ = (∑ j, (Δ : Ω) * v c j * ((M : Ω) * s j * w)) ^ t := by
            rw [Finset.sum_pow', Fintype.piFinset_univ]
        _ = ((Δ * M : ℕ) : Ω) ^ t := by rw [hbase]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpread =====
