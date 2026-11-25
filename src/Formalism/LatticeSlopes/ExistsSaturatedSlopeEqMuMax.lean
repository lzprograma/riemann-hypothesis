module

public import Formalism.LatticeSlopes.CovolAntiSameRank
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
public import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot
public import Formalism.LatticeSlopes.LatticeSlopesProofs.SaturationProperties
public import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
public import Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxAttained
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
public import Formalism.LatticeSlopes.LatticeSlopesProofs.GramDetLe
public import Formalism.LatticeSlopes.LatticeSlopesProofs.OrthSum
import Mathlib.Tactic.Linter.HaveILetI
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqCovolume
import Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector
import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeLeMuMaxOf
import Formalism.LatticeSlopes.LatticeSlopesProofs.SlopesBdd

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LatticeSlopes.LatticeSlopesProofs.FiniteSaturated, Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxLeMin, Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax

-- ===== clump member: Formalism.LatticeSlopes.LatticeSlopesProofs.FiniteSaturated =====
-- clump-header: {"m": "Formalism.LatticeSlopes.LatticeSlopesProofs.FiniteSaturated", "h": "module\n\npublic import Formalism.LatticeSlopes.CovolAntiSameRank\npublic import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos\npublic import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot\npublic import Formalism.LatticeSlopes.LatticeSlopesProofs.SaturationProperties\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Module Submodule

noncomputable section

namespace Formalism.F

universe u

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem finite_mem_norm_le (L : Submodule ℤ E) [hL : DiscreteTopology L] (C : ℝ) :
    {v : E | v ∈ L ∧ ‖v‖ ≤ C}.Finite :=
  (Metric.finite_isBounded_inter_isClosed (isDiscrete_iff_discreteTopology.mpr hL)
    (Metric.isBounded_closedBall (x := (0 : E)) (r := C))
    L.toAddSubgroup.isClosed_of_discreteTopology).subset fun _ hv =>
    ⟨mem_closedBall_zero_iff.mpr hv.2, hv.1⟩

theorem sub_mem_of_starProjection_eq (W : Submodule ℝ E) {x z : E}
    (h : Wᗮ.starProjection x = Wᗮ.starProjection z) : x - z ∈ W := by
  have h0 : Wᗮ.starProjection (x - z) = 0 := by rw [map_sub, h, sub_self]
  rwa [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at h0

theorem mem_of_starProjection_mem_span_orthQuotient {L M N₁ : Submodule ℤ E} (hM : IsSaturated L M) (h1 : N₁ ≤ M)
    {x : E} (hx : x ∈ L)
    (hπ : (span ℝ (N₁ : Set E))ᗮ.starProjection x ∈ span ℝ (quot M N₁ : Set E)) : x ∈ M := by
  change (span ℝ (N₁ : Set E))ᗮ.starProjection x ∈
    span ℝ (((span ℝ (N₁ : Set E))ᗮ.starProjection : E →ₗ[ℝ] E) '' (M : Set E)) at hπ
  rw [Submodule.span_image, Submodule.mem_map] at hπ
  obtain ⟨y, hy, hyx⟩ := hπ
  exact hM.2 x hx (sub_add_cancel x y ▸ add_mem (span_mono h1 (sub_mem_of_starProjection_eq _ hyx.symm)) hy)

end

private theorem rk_pos_of_ne_zero_mem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (N : Submodule ℤ E) [DiscreteTopology N]
    {v : E} (hv : v ∈ N) (hv0 : v ≠ 0) : 0 < rk N :=
  Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hv⟩, by simpa using hv0⟩

theorem finite_saturated_rank_le_covol_le (hS : ShortVector.{u}) {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (k : ℕ) :
    ∀ (L : Submodule ℤ E), DiscreteTopology L → ∀ X : ℝ,
      {N : Submodule ℤ E | IsSaturated L N ∧ rk N ≤ k ∧ covol N ≤ X}.Finite := by
  induction k with
  | zero =>
    intro L hL X
    refine (Set.finite_singleton (⊥ : Submodule ℤ E)).subset ?_
    rintro N ⟨hN, hrk, -⟩
    have : DiscreteTopology N := discreteTopology_of_le hN.1
    by_contra hne
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hne
    have := rk_pos_of_ne_zero_mem N hv hv0
    omega
  | succ k ih =>
    intro L hL X
    have hB : {v : E | v ∈ L ∧ ‖v‖ ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) * max 1 X ∧ v ≠ 0}.Finite :=
      (finite_mem_norm_le L _).subset fun _ hv => ⟨hv.1, hv.2.1⟩
    refine ((Set.finite_singleton ⊥).union (hB.biUnion (t := fun v =>
      {N : Submodule ℤ E | IsSaturated L N ∧ rk N ≤ k + 1 ∧ covol N ≤ X ∧
        satur L (span ℤ ({v} : Set E)) ≤ N}) fun v ⟨hvL, _, hv0⟩ => ?_)).subset ?_
    · have hspL : span ℤ ({v} : Set E) ≤ L := span_le.mpr (Set.singleton_subset_iff.mpr hvL)
      obtain ⟨sat1, -, hrk1⟩ := saturation_properties E L _ hL hspL
      have : DiscreteTopology (span ℤ ({v} : Set E)) := discreteTopology_of_le hspL
      have hrksp : 0 < rk (span ℤ ({v} : Set E)) :=
        rk_pos_of_ne_zero_mem _ (mem_span_singleton_self v) hv0
      have dq := degree_quotient E L _ hL sat1
      have hc1 : 0 < covol (satur L (span ℤ ({v} : Set E))) := covol_pos' E _ (discreteTopology_of_le sat1.1)
      have hfin := ih (quot L (satur L (span ℤ ({v} : Set E)))) dq.1
        (X / covol (satur L (span ℤ ({v} : Set E))))
      refine Set.Finite.of_finite_image (f := fun N => quot N (satur L (span ℤ ({v} : Set E))))
        (hfin.subset ?_) ?_
      · rintro _ ⟨N, ⟨hN, hrkN, hcov, h1⟩, rfl⟩
        have hdN := discreteTopology_of_le (L := L) hN.1
        have dqN := degree_quotient E N _ hdN ⟨h1, fun x hx hxs => sat1.2 x (hN.1 hx) hxs⟩
        have hcQ := covol_pos' E _ dqN.1
        have hcN := covol_pos' E N hdN
        have hmul : covol N = covol (satur L (span ℤ ({v} : Set E))) *
            covol (quot N (satur L (span ℤ ({v} : Set E)))) := by
          apply Real.log_injOn_pos hcN (mul_pos hc1 hcQ)
          rw [Real.log_mul hc1.ne' hcQ.ne']
          have := dqN.2.2; unfold deg at this; linarith
        refine ⟨⟨Submodule.map_mono hN.1, ?_⟩, by dsimp only; have := dqN.2.1; omega, ?_⟩
        · rintro _ ⟨x, hxL, rfl⟩ hys
          exact Submodule.mem_map_of_mem (mem_of_starProjection_mem_span_orthQuotient hN h1 hxL hys)
        · rw [le_div_iff₀ hc1, mul_comm, ← hmul]; exact hcov
      · intro N hN N' hN' heq
        have key : ∀ {A B : Submodule ℤ E}, IsSaturated L B → satur L (span ℤ ({v} : Set E)) ≤ B →
            quot A (satur L (span ℤ ({v} : Set E))) = quot B (satur L (span ℤ ({v} : Set E))) →
            A ≤ L → A ≤ B := fun hB hB1 hAB hAL x hx =>
          mem_of_starProjection_mem_span_orthQuotient hB hB1 (hAL hx)
            (hAB ▸ subset_span (Submodule.mem_map_of_mem hx))
        exact le_antisymm (key hN'.1 hN'.2.2.2 heq hN.1.1) (key hN.1 hN.2.2.2 heq.symm hN'.1.1)
    · rintro N ⟨hN, hrk, hcov⟩
      by_cases hbot : N = ⊥
      · exact Or.inl hbot
      right
      have hdN := discreteTopology_of_le (L := L) hN.1
      obtain ⟨v, hvN, hv0, hvle⟩ := hS E N hdN hbot
      have hr := rk_pos_of_ne_zero_mem N hvN hv0
      have hcN := covol_pos' E N hdN
      have hpow : covol N ^ ((1 : ℝ) / (rk N : ℝ)) ≤ max 1 X := by
        have he : (1 : ℝ) / (rk N : ℝ) ≤ 1 :=
          (div_le_one (by exact_mod_cast hr)).mpr (by exact_mod_cast hr)
        rcases le_or_gt (covol N) 1 with h | h
        · exact (Real.rpow_le_one hcN.le h (by positivity)).trans (le_max_left _ _)
        · exact ((Real.rpow_le_rpow_of_exponent_le h.le he).trans_eq (Real.rpow_one _)).trans
            (hcov.trans (le_max_right _ _))
      have hnorm : ‖v‖ ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) * max 1 X :=
        hvle.trans (mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hrk)) hpow
          (by positivity) (Real.sqrt_nonneg _))
      refine Set.mem_biUnion (x := v) ⟨hN.1 hvN, hnorm, hv0⟩ ⟨hN, hrk, hcov, fun x hx => ?_⟩
      exact hN.2 x hx.1 (span_mono (span_le.mpr (Set.singleton_subset_iff.mpr hvN)) hx.2)

theorem finiteSaturated_of (hS : ShortVector.{u}) : FiniteSaturated.{u} := by
  intro E _ _ _ L hL X
  exact (finite_saturated_rank_le_covol_le hS (rk L) L hL X).subset fun N ⟨hN, hX⟩ =>
    ⟨hN, by have := (degree_quotient E L N hL hN).2.1; omega, hX⟩

end Formalism.F
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LatticeSlopes.LatticeSlopesProofs.FiniteSaturated =====

-- ===== clump member: Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxLeMin =====
-- clump-header: {"m": "Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxLeMin", "h": "module\n\npublic import Formalism.LatticeSlopes.CovolAntiSameRank\npublic import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe\npublic import Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxAttained\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Module

namespace Formalism.F

universe u

theorem muMaxLeMin_of (hP : CovolPos.{u}) (hS : ShortVector.{u}) : MuMaxLeMin.{u} := by
  intro E _ _ _ L hL hL0 r hr hmin
  haveI := hL
  have hne : (slopes L).Nonempty := ⟨slope L, L, le_rfl, hL0, rfl⟩
  unfold muMax
  apply csSup_le hne
  rintro t ⟨N, hNL, hN0, rfl⟩
  haveI : DiscreteTopology N := discreteTopology_of_le hNL
  have hk : 0 < rk N := att_rk_pos hN0
  have hkL : rk N ≤ rk L := att_rk_le hNL
  have hc : 0 < covol N := hP E N inferInstance
  obtain ⟨v, hvN, hv0, hvle⟩ := hS E N inferInstance hN0
  have hrv : r ≤ ‖v‖ := hmin v (hNL hvN) hv0
  have hk' : (0 : ℝ) < (rk N : ℝ) := by exact_mod_cast hk

  have h1 : Real.log r ≤ Real.log (rk N : ℝ) / 2 + Real.log (covol N) / (rk N : ℝ) := by
    have hpow : 0 < covol N ^ ((1 : ℝ) / (rk N : ℝ)) := Real.rpow_pos_of_pos hc _
    have hsq : 0 < Real.sqrt (rk N : ℝ) := Real.sqrt_pos.mpr hk'
    have h := Real.log_le_log hr (hrv.trans hvle)
    rw [Real.log_mul hsq.ne' hpow.ne', Real.log_sqrt hk'.le, Real.log_rpow hc] at h
    have e : (1 : ℝ) / (rk N : ℝ) * Real.log (covol N) = Real.log (covol N) / (rk N : ℝ) := by ring
    linarith
  have h2 : Real.log (rk N : ℝ) ≤ Real.log (rk L : ℝ) :=
    Real.log_le_log hk' (by exact_mod_cast hkL)
  have h3 : slope N = -(Real.log (covol N) / (rk N : ℝ)) := by
    unfold slope deg; ring
  rw [h3]
  linarith

end Formalism.F
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxLeMin =====

-- ===== clump member: Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax =====
-- clump-header: {"m": "Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax", "h": "module\n\npublic import Formalism.LatticeSlopes.CovolAntiSameRank\nimport Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqCovolume\npublic import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram\npublic import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos\npublic import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot\nimport Formalism.LatticeSlopes.LatticeSlopesProofs.FiniteSaturated\npublic import Formalism.LatticeSlopes.LatticeSlopesProofs.GramDetLe\npublic import Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxLeMin\npublic import Formalism.LatticeSlopes.LatticeSlopesProofs.OrthSum\npublic import Formalism.LatticeSlopes.LatticeSlopesProofs.SaturationProperties\nimport Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector\nimport Formalism.LatticeSlopes.LatticeSlopesProofs.SlopeLeMuMaxOf\nimport Formalism.LatticeSlopes.LatticeSlopesProofs.SlopesBdd\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.F

alias covolEqGram := _root_.Formalism.F.covol_eq_gram
theorem slopesBdd : SlopesBdd := slopesBdd_of _root_.Formalism.F.gram_det_le
theorem slopeLeMuMax : SlopeLeMuMax := slopeLeMuMax_of slopesBdd
alias degQuot := _root_.Formalism.F.degree_quotient
alias saturProps := _root_.Formalism.F.saturation_properties
theorem shortVector : ShortVector := shortVector_of _root_.Formalism.F.covol_eq_covolume'
theorem finiteSaturated : FiniteSaturated := finiteSaturated_of shortVector
theorem muMaxLeMin : MuMaxLeMin := muMaxLeMin_of _root_.Formalism.F.covol_pos' shortVector
alias orthSum := _root_.Formalism.F.orthogonal_sum_slope

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

alias covol_pos := _root_.Formalism.F.covol_pos_of_discrete

theorem deg_eq_deg_add_deg_quot {L N : Submodule ℤ E} [DiscreteTopology L] (hN : IsSaturated L N) :
    deg L = deg N + deg (quot L N) :=
  (degQuot E L N ‹_› hN).2.2

end

end Formalism.F
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax =====
