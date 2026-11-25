module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndEnc
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndVerb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndVerbB
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EvalSinglePointId
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActOf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqChart
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.KillAddVal
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGauge
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEigPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PsiCover

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndAll, Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndTop

-- ===== clump member: Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndAll =====
-- clump-header: {"m": "Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndAll", "h": "module\n\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndEnc\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndVerb\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndVerbB\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EvalSinglePointId\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActOf\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf\nimport Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqChart\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqPf\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvPf\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.KillAddVal\nimport Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEigPf\nimport Formalism.SharpRestriction.Divisibility.GeneratorPowers.PsiCover\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open ReciprocityTheory.ChartRestriction.G.Out NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem chartIndep2_of_open (hGauge : ExpGaugeOfSt) (hKill : KillAddValSt) (hGlob : GlobalFnsSt)
    (hFix : FrTruncFixSt) (hInv : HarmInvSt) : ChartIndepSt2 :=
  chartIndep2_of_fix
    (chartIndepTrunc_of (expChartOf_of (expActOf_of linEigSt_holds)) hGauge tie_holds ExpUniqChart.expUniqTan
      (gaugeUniq_of_global hGlob) hKill)
    hFix germFix_holds hInv

theorem chartIndep2_of_open' (hGauge : ExpGaugeOfSt) (hPsi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E), PsiCoverSt H) (hGlob : GlobalFnsSt) (hFix : FrTruncFixSt) (hInv : HarmInvSt) : ChartIndepSt2 :=
  chartIndep2_of_open hGauge (killAddVal_of hPsi) hGlob hFix hInv

theorem chartIndep2_of_open'' (hGauge : ExpGaugeOfSt) (hGlob : GlobalFnsSt) (hFix : FrTruncFixSt)
    (hInv : HarmInvSt) : ChartIndepSt2 :=
  chartIndep2_of_open' hGauge (fun _ _ _ _ H => psiCover_holds H) hGlob hFix hInv

theorem chartIndep2_of_gauge (hGauge : ExpGaugeOfSt) (hGlob : GlobalFnsSt) (hFix : FrTruncFixSt) : ChartIndepSt2 :=
  chartIndep2_of_open'' hGauge hGlob hFix (harmInv_of (expActOf_of linEigSt_holds))

end Formalism.MainNotions.ModuliIntegralCharts.H1
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndAll =====

-- ===== clump member: Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndTop =====
-- clump-header: {"m": "Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndTop", "h": "module\n\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndAll\nimport Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActOf\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGauge\npublic import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio\nimport Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEigPf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField

theorem chartIndep2_of_gauge_glob (hGauge : ExpGaugeOfSt) (hGlob : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) : ChartIndepSt2 :=
  chartIndep2_of_gauge hGauge hGlob frTruncFix_holds

theorem chartIndep2_of_glob (hGlob : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) : ChartIndepSt2 :=
  chartIndep2_of_gauge_glob (ExpGauge.expGaugeOf_of (expActOf_of linEigSt_holds)) hGlob


end Formalism.MainNotions.ModuliIntegralCharts.H1
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndTop =====
