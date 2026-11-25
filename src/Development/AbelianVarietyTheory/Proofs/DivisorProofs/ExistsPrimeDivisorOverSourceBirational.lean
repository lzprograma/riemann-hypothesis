module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem DivOver.exists_over : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E : DivOver p, ∃ E' : DivOver (s ≫ p), DivOver.Over s E' E := by
  intro k _ X Y _ _ p s _ hs E
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap s) hs
  let V : ValuationSubring Y.functionField := E.ring.comap e.symm.toRingHom
  have hV (f : X.functionField) : f ∈ E.ring ↔ functionFieldMap s f ∈ V := by
    change f ∈ E.ring ↔ e.symm (e f) ∈ E.ring
    rw [e.symm_apply_apply]
  let φ : E.ring →+* V :=
    ((functionFieldMap s).comp E.ring.subtype).codRestrict V fun a => (hV _).1 a.2
  have hφ : Function.Bijective φ :=
    ⟨fun _ _ h => Subtype.ext (hs.1 (congrArg Subtype.val h)),
      fun f => ⟨⟨e.symm f.1, f.2⟩, Subtype.ext (e.apply_symm_apply f.1)⟩⟩
  have hc (a : k) : functionFieldMap s (Cartier.constFn p a) = Cartier.constFn (s ≫ p) a :=
    RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p s) a
  refine ⟨⟨V, fun a => hc a ▸ (hV _).1 (E.const_mem a),
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (RingEquiv.ofBijective φ hφ), ?_⟩, hV⟩
  have h3 := E.essFiniteType.comp (RingHom.FiniteType.of_surjective φ hφ.2).essFiniteType
  convert h3 using 1
  exact RingHom.ext fun a => Subtype.ext (hc a).symm

end GlobalTheory.Discrepancy
