module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicParamOfDegZeroCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterFunctionEqZeroOfComposable

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichCharts, Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichChartsStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichCharts =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichCharts", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicParamOfDegZeroCompatibleStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterFunctionEqZeroOfComposable\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}

theorem perCl_injective (K : Charts F) (hK : K.Rich) (per per' : Λ →+ Hol F.V)
    (h : K.perCl per = K.perCl per') : per = per' := by
  obtain ⟨G, hG⟩ := (H1.mk_eq_mk (F := K.Oc)).1 h

  have hd : ∀ (T T' : K.Obj) (φ : T ⟶ T'), G T' - φ.φ (G T) =
      algebraMap (Hol F.V) T'.C (per φ.deg) - algebraMap (Hol F.V) T'.C (per' φ.deg) := by
    intro T T' φ
    have := congrFun (congrFun (congrFun hG T) T') φ
    exact this

  have h0 : ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T) := by
    intro T T' φ hφ
    have := hd T T' φ
    simp only [hφ, map_zero, sub_zero] at this
    exact sub_eq_zero.1 this
  obtain ⟨p, hp⟩ := _root_.GlobalTheory.AnPer.Charts.exists_param_of_deg_zero K hK G h0

  have hv : ∀ (T T' : K.Obj) (φ : T ⟶ T'), algebraMap (Hol F.V) T'.C (per φ.deg - per' φ.deg) = 0 := by
    intro T T' φ
    have := hd T T' φ
    rw [hp T, hp T', AlgHom.commutes, sub_self] at this
    exact ((algebraMap (Hol F.V) T'.C).map_sub (per φ.deg) (per' φ.deg)).trans this.symm
  ext l : 1
  rw [← sub_eq_zero]
  refine _root_.GlobalTheory.AnPer.Charts.eq_zero_of_cst_composable K hK l 0 (per l - per' l) fun k k' k'' e e' ↦ ?_
  have h1 : K.cst k' (per l - per' l) = 0 := hv _ _ (ptHom (K.triv k') e)
  rw [← sh_cst e' (per l - per' l), h1, map_zero]

end GlobalTheory.AnPer.Charts
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichCharts =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichChartsStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichChartsStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichCharts\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichChartsStatement =====
