module

public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters

structure SignedPar (n : ℕ) where
  lam : Fin n → ℝ
  sgn : Fin n → Bool
  hc : Formalism.QuantumDeterminants.IsHCParam lam

namespace SignedPar

variable {n : ℕ} (P : SignedPar n)

def p : ℕ := (Finset.univ.filter fun a => P.sgn a = true).card

def q : ℕ := (Finset.univ.filter fun a => P.sgn a = false).card

def IsOfSig (p q : ℕ) : Prop := P.p = p ∧ P.q = q

def low : Fin n → ℝ := Formalism.QuantumDeterminants.lowK P.sgn P.lam

end SignedPar

section Chains

variable {R : Ranks} (c : HCParam R)

end Chains

section Adelic

variable {D : D7}

def gramAt (V : HSp D) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ := V.gram.map (tauE D τ)

end Adelic

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsDSPar {n : ℕ} (P : SignedPar n) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  IsDS P.sgn P.lam σ

end Rep

section Signatures

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

end Signatures

end GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters
