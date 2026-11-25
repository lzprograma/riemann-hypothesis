module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetNeZeroOfHasSignature
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

noncomputable section

namespace GlobalTheory.BottomIsom

theorem hasSignature_map_star {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.UG.HasSignature M p q) :
    Formalism.UG.HasSignature (M.map (starRingEnd ℂ)) p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨e, Matrix.GeneralLinearGroup.map (starRingEnd ℂ) P, ?_⟩
  have := congrArg (fun A => Matrix.map A (starRingEnd ℂ)) hP
  simp only [Matrix.map_mul] at this
  have hJ : (Formalism.UG.Jpq p q : Matrix _ _ ℂ).map (starRingEnd ℂ) = Formalism.UG.Jpq p q := by
    ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite]
  rw [hJ] at this
  exact this

theorem hasSignature_all {D : D7} {V : HSp D} (h : NegIdx V 0) (σ : D.host.E →+* ℂ) :
    Formalism.UG.HasSignature (V.gram.map σ) V.rank 0 := by
  obtain ⟨τ, hσ | hσ⟩ := GlobalTheory.DefiniteMult.exists_tauE_or_conj D σ
  · subst hσ
    simpa [gramAt] using h τ
  · subst hσ
    have h1 := hasSignature_map_star (by simpa [gramAt] using h τ)
    rw [Matrix.map_map] at h1
    exact h1

def posResign {D : D7} (V : HSp D) : HSp D := { V with sig := fun _ => (V.rank, 0) }

theorem posResign_sigOK {D : D7} {V : HSp D} (h : NegIdx V 0) : (posResign V).SigOK := fun σ =>
  hasSignature_all h σ

theorem isoMat_of_posDef : ∀ {D : D7} {V V' : HSp D}, V.rank = V'.rank → NegIdx V 0 → NegIdx V' 0 →
    Nonempty (GlobalTheory.Mem.Isom.IsoMat V V') := by
  intro D V V' hr h h'
  obtain ⟨φ, hφ⟩ := GlobalTheory.LandherrSignature.exists_isometry_host D (posResign V) (posResign V')
    (posResign_sigOK h) (posResign_sigOK h') hr (fun _ => by simp [posResign, hr])
  exact ⟨GlobalTheory.Mem.Isom.IsoMat.ofEquiv φ hφ⟩

end GlobalTheory.BottomIsom
