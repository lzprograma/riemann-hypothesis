module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.RawLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure Laws (R : RealDat D A Ks) (F : Face D A) : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  thP : R.IsThP

def thetaIP {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (f f' : WO S T' → ℂ) : ℂ :=
  ∫ w in 𝓕, star (f w) * f' w ∂μ

def upLift {V W : HSp D} (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓖 : Set (GA D W))
    (f : WO V W → ℂ) (φ : GA D W → ℂ) : GA D V → ℂ :=
  fun h => ∫ g in 𝓖, star (thetaKO om h g f) * φ g ∂ν

theorem thetaInner_smul_left {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (a : ℂ) (f f' : WO S T' → ℂ) :
    thetaIP μ 𝓕 (a • f) f' = star a * thetaIP μ 𝓕 f f' := by
  unfold thetaIP
  rw [← integral_const_mul]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]

theorem thetaInner_smul_right {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (a : ℂ) (f f' : WO S T' → ℂ) :
    thetaIP μ 𝓕 f (a • f') = a * thetaIP μ 𝓕 f f' := by
  unfold thetaIP
  rw [← integral_const_mul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]

end GlobalTheory.RawLift

end
