module

public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupJetsChart
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLocalHomValuationExtension
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct

namespace GlobalTheory.CharDepth

theorem nonempty_unifChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), y.IsAlg → ∀ (p : ℕ) [Fact p.Prime] (X : ValExt T p), Nonempty (UnifChart Ch X) := by
  intro E _ _ _ H Dw l Xo c T io y Ch hy p _ X
  let _ := H.starRing
  obtain ⟨T', φ, t', m, hi, hf, -, -, P, -⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T Ch.I.G Ch.I.t' Ch.I.m2 _ Ch.I.m1 hy
  obtain ⟨ι', hl, hι⟩ := ValExt.exists_local_extension T T' φ hi hf p X
  obtain ⟨F', x', act', hF, hA, hc, ha⟩ := GlobalTheory.integralChart_baseChange E H Dw l Xo c T io y Ch T' φ t' m
  have key : ∀ {σ : Type} (f : MvPowerSeries σ T.V),
      MvPowerSeries.map ι' (MvPowerSeries.map φ f) = MvPowerSeries.map X.ι f := by
    intro σ f
    ext n
    simp only [MvPowerSeries.coeff_map, ← hι, RingHom.comp_apply]
  refine ⟨⟨T', ι', hl, t', P, F', x', hc, act', ha, ?_, fun a => ?_⟩⟩
  · funext i
    show MvPowerSeries.map ι' (F'.F i) = _
    rw [hF]
    exact key _
  · funext i
    show MvPowerSeries.map ι' (act'.act a i) = _
    rw [hA]
    exact key _

end GlobalTheory.CharDepth
