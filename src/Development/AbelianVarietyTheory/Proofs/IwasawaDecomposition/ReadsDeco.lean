module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
public import Formalism.LocalToGlobal.Columns.Adelic
public import Formalism.LocalToGlobal.Columns.RowFormsAdelic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.RowAd

variable (X : Stages)

theorem rank_X' : X.toD7.sp.X'.rank = X.B.R.N X.B.R.m - 1 := by
  rw [X.toD7.sp.X'_rank, Formalism.L2.Col.rank_X'_eq]
  rfl

def ptE (h : Bridge.Gf X.toD7.sp.X') :
    GL (Fin (X.B.R.N X.B.R.m - 1)) (X.B.fields.E ⊗[X.B.fields.F] Formalism.L2.Herm.Af X.B.fields.F) :=
  Units.map (Matrix.reindexAlgEquiv (Formalism.IndefR.Lev.EAf X.toD7) (Formalism.IndefR.Lev.EAf X.toD7) (finCongr (rank_X' X))).toMonoidHom
    (Formalism.UG.bc (Formalism.IndefR.Lev.swapAE X.toD7) h.1)

variable {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) {U : Set I.ι}

def decoAd (t : TupU I U) (h : Bridge.Gf X.toD7.sp.X') : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).D :=
  Formalism.L2.Col.decoOf (F := X.B.fields.F) (E := X.B.fields.E) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) (ptE X h)

def ReadsDeco (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (cX : CoefA X.toD7.sp.X') {J : Subgroup (Bridge.Gf X.toD7.sp.X')}
    {χ : J →* ℂˣ} (t : TupU I U)
    (P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ J χ) : Prop :=
  ∃ m : ((famR X I hX U Xg tr).A.MtildeCSD t).V →ₛₗ[X.toD7.what₂.embLL] cX.W,
    ∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'),
      P.ext (f : _ → _) h = m ((((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1
        (decoAd X I t h))

end GlobalTheory.Mem.R3.RowAd
