module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TilX Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.TopPtModel

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_mul {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (a b : GL (Fin N) (AfE F E)) :
    ((a * b : GL (Fin N) (AfE F E)).1).map (adAt F P) = a.1.map (adAt F P) * b.1.map (adAt F P) := by
  rw [Units.val_mul, Matrix.map_mul]

theorem adAt_of_prV {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) {k : GL (Fin N) (AfE F E)}
    (h1 : bc (prV (E := E) (P.under (𝓞 F))) k = 1) : k.1.map (adAt F P) = 1 := by
  refine Matrix.ext fun i j => ?_
  have h2 : prV (E := E) (P.under (𝓞 F)) (k.1 i j - (1 : Matrix (Fin N) (Fin N) (AfE F E)) i j) = 0 := by
    have h3 := congrArg (fun g : GL (Fin N) _ => g.1 i j) h1
    simp only [Units.val_one] at h3
    have h4 : prV (E := E) (P.under (𝓞 F)) (k.1 i j) = (1 : Matrix (Fin N) (Fin N) _) i j := h3
    rw [map_sub, h4, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 := adAt_eq_zero_of_prV P _ h2
  rw [map_sub, sub_eq_zero] at h3
  refine h3.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Gen

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

theorem topPt_base {u : B.Word} {a : I.ι} {k : GA B (B.R.N B.R.m)} [NeZero (B.R.N B.R.m - 1)] (h : I.TopPt l Z u a k) :
    PtOf k (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u (DecoF.base _ _ _ _ _)) := by
  have := h (DecoF.base _ _ _ _ _) 1 1 (isPtOf_base _) ⟨(Matrix.one_mul _).trans (Matrix.mul_one _).symm, Matrix.one_mulVec _⟩
  rwa [one_mul] at this

end GlobalTheory.Mem.Col2.TopPtModel

end
