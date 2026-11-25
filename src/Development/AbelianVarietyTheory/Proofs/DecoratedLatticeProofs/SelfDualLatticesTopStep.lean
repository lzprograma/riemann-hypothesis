module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConsecutiveStep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TopMove

section Package

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem weil_rec {n k : ℕ} (e : n = k) {χS χT : (AE D)ˣ →* Circle} {o : Om (Yc D n) D.sp.X'}
    (h : IsWeilDatumO R.ψ (Yc D n) D.sp.X' χS χT o) :
    IsWeilDatumO R.ψ (Yc D k) D.sp.X' χS χT (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') o e) := by
  subst e
  exact h

theorem vac_rec {n k : ℕ} (e : n = k) {f : WO (Yc D n) D.sp.X' → ℂ}
    (h : IsVacO R.ψ R.θ (Yc D n) D.sp.X' (cart (R.MY n)) (cart R.MX) (R.ΛY n) R.ΛX f) :
    IsVacO R.ψ R.θ (Yc D k) D.sp.X' (cart (R.MY k)) (cart R.MX) (R.ΛY k) R.ΛX
      (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) f e) := by
  subst e
  exact h

theorem weil_omT (hω : R.chain_ωX) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsWeilDatumO R.ψ (Yc D (j + 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 (omT R t j h) :=
  weil_rec R (idx_top h) (hω t)

theorem isVacO_vacT (hv : R.chain_vX) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsVacO R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX) (R.ΛY (j + 1)) R.ΛX (vacT R j h) :=
  vac_rec R (idx_top h) (hv t).1

end Package

end GlobalTheory.TopMove

end
