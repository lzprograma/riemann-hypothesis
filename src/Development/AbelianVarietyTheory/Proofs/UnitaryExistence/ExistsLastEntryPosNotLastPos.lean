module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorsDisjointColumnsHarmonic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorMonomials
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
import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Rt0ConjNegNeZero
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.JetRangeLevelFactor, Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLastEntryPosNotLastPos

-- ===== clump member: Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.JetRangeLevelFactor =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.JetRangeLevelFactor", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Formalism.LocalToGlobal.ProjectiveLattices.RowDeg\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def RowsDominant (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∀ τ : E →+* ℂ, Antitone fun i : Fin (Dw.mult τ) => a (τ, i)

variable {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

end GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.JetRangeLevelFactor =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLastEntryPosNotLastPos =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLastEntryPosNotLastPos", "h": "module\n\nimport Development.WeilBound.CoreStatements.PlurisubharmonicCones.Rt0ConjNegNeZero\npublic import Formalism.LocalToGlobal.ProjectiveLattices.ThProps\npublic import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.JetRangeLevelFactor\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorsDisjointColumnsHarmonic\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorMonomials\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Formalism.LocalToGlobal.ProjectiveLattices.JFDFree\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.ThetaClaimsCompare

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  apply LevelTowerAlt.rt0_conj_neg_ne_zero

theorem not_inPsi_conjugate {τ : E →+* ℂ} (h : InPsi H τ) : ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h'
  unfold InPsi at h h'
  rw [ComplexEmbedding.conjugate_coe_eq, h, (rt0_conj_neg_ne_zero H).1] at h'
  exact (rt0_conj_neg_ne_zero H).2 (by linear_combination (-1 / 2 : ℂ) * h')

theorem mult_of_inPsi {τ : E →+* ℂ} (h : InPsi H τ) : Dw.mult τ = Dw.p := ite_eq_left h

theorem mult_of_not_inPsi {τ : E →+* ℂ} (h : ¬ InPsi H τ) : Dw.mult τ = Dw.q := ite_eq_right h

def trunc (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : (E →+* ℂ) × ℕ → ℕ :=
  fun x => if x.2 < Dw.mult x.1 then a x else 0

theorem trunc_row (a : (E →+* ℂ) × ℕ → ℕ) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : trunc Dw a (τ, i) = a (τ, i) :=
  ite_eq_left i.isLt

theorem rowsDominant_of_dom {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (h : Dom a n) : RowsDominant Dw a :=
  fun τ _ _ hij => h.1 τ hij

theorem antitone_trunc {a : (E →+* ℂ) × ℕ → ℕ} (h : RowsDominant Dw a) (τ : E →+* ℂ) :
    Antitone fun i => trunc Dw a (τ, i) := by
  intro i j hij
  simp only [trunc]
  split_ifs with hj hi hi
  · exact h τ (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

theorem df_trunc (a : (E →+* ℂ) × ℕ → ℕ) : DF Dw (trunc Dw a) = DF Dw a := by
  simp only [DF, trunc_row]

variable (Xo : Moduli Dw l) (c : Coeff l)

theorem harmA_trunc (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    harmA (Dw := Dw) c (trunc Dw a) n = harmA (Dw := Dw) c a n := by
  ext P
  simp only [harmA, HaO, HHa, RowDeg, Set.mem_setOf_eq, trunc_row]

open GlobalTheory.BlockProdEx in
theorem exists_harmA_ne_zero {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (ha : RowsDominant Dw a) (hn : Dw.p + Dw.q ≤ n) :
    ∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0 := by
  classical
  let col : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin n := fun τ i =>
    if h : InPsi H τ then ⟨i, by have := i.isLt; have := mult_of_inPsi (Dw := Dw) h; omega⟩
    else ⟨Dw.p + i, by have := i.isLt; have := mult_of_not_inPsi (Dw := Dw) h; omega⟩
  have hinj : ∀ τ, Function.Injective (col τ) := by
    intro τ i j hij
    have := congrArg Fin.val hij
    by_cases h : InPsi H τ
    · simp only [col, dite_eq_left h] at this
      exact Fin.ext this
    · simp only [col, dite_eq_right h] at this
      exact Fin.ext (by omega)
  have hdis : ∀ τ, InPsi H τ → ∀ i j, col τ i ≠ col (ComplexEmbedding.conjugate τ) j := by
    intro τ h i j hij
    have := congrArg Fin.val hij
    simp only [col, dite_eq_left h, dite_eq_right (not_inPsi_conjugate h)] at this
    have := i.isLt
    have := mult_of_inPsi (Dw := Dw) h
    omega
  let cols (τ : E →+* ℂ) (s : Fin (Dw.mult τ)) (j : Fin (s + 1)) := col τ (Fin.castLE s.isLt j)
  rw [← harmA_trunc]
  refine ⟨minorsP Dw.mult n cols c.F fun τ i => trunc Dw a (τ, i), ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact minorMonomial_mem_harmonic _ _ _ cols _ _
      (fun τ h s s' i j => hdis τ h (Fin.castLE s.isLt i) (Fin.castLE s'.isLt j)) _
  · exact minorMonomial_rowInvariant _ _ _ cols _
  · exact minorMonomial_rowDegree _ _ _ cols _ (antitone_trunc ha) fun τ => ite_eq_right (lt_irrefl _)
  · exact minorMonomial_coeff_mem Dw.mult n c.F cols _ _
  · exact minorMonomial_ne_zero _ _ _ cols (fun τ s => (hinj τ).comp (Fin.castLE_injective s.isLt)) _

variable {Xo c}

end GlobalTheory.ThetaClaimsCompare
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLastEntryPosNotLastPos =====
