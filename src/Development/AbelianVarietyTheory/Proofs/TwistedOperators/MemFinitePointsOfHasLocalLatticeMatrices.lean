module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
noncomputable section

namespace GlobalTheory.RowCover

theorem mem_GfC_of_hasLoc : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x : GA D (G.V (.grid D.R.m j)))
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → x ∈ GfC _ := by
  intro D T L sc G t B j hj x g hx
  obtain ⟨e, ⟨⟨es, hes, rfl⟩, -⟩, hg, -⟩ := hx
  have h0 : infPart D ((∑ PP ∈ locPl G t, es PP) + cA D (∑ PP ∈ locPl G t, es PP)) = 0 := by

    rw [map_sum (cA D), ← Finset.sum_add_distrib, map_sum]
    refine Finset.sum_eq_zero fun PP hPP => ?_
    obtain ⟨-, -, v, ε, ⟨α, rfl, -⟩, h⟩ := (hes PP hPP).1
    rw [h]; exact TensorProduct.zero_tmul _ _
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := congrArg (infPart D) (hg i j)
  rw [map_mul, h0, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at this
  refine Eq.trans this ?_
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end GlobalTheory.RowCover
