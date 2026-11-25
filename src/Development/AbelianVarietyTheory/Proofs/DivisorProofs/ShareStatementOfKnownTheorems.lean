module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CovTop.ShareRowsNef

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) {la : AllWt.Weight Dw} (h : GapGe 1 la) :
    (∀ τ, Antitone (la τ)) ∧ ∀ τ, 1 ≤ gap (la τ) (Dw.p - 1) := by
  refine ⟨fun τ => ?_, fun τ => h τ _ (by omega)⟩
  have key : ∀ (n : ℕ) (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + n → la τ b ≤ la τ a := by
    intro n
    induction n with
    | zero => intro a b e; rw [show b = a from Fin.ext e]
    | succ n ih =>
      intro a b e
      have h1 := ih a ⟨a + n, by omega⟩ rfl
      have h2 := h τ (a + n) (by omega)
      rw [gap_eq (la τ) (i := ⟨a + n, by omega⟩) (j := b) e] at h2
      omega
  intro a b hab
  exact key (b - a) a b (by have : (a : ℕ) ≤ b := hab; omega)

theorem gapGe_of_wtBig {P : WtPar Dw} (h : WtBig P) : GapGe 1 P.u₁ ∧ GapGe 1 P.u₂ ∧ ∀ j, GapGe 1 (P.wt j) := by
  have h3 : GapGe 3 P.u₁ := h.gaps.mono (by
    have : 3 * 1 ≤ (FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    exact_mod_cast this)
  have h2 : ∀ τ k, k + 1 < Dw.p + Dw.q → 3 ≤ gap (P.u₂ τ) k := fun τ k hk => by
    have a := h3 τ k hk
    have b := (P.gap_rem τ k).1
    simp only [gap, dite_eq_left hk, WtPar.u₂, Pi.add_apply] at a b ⊢
    omega
  refine ⟨h3.mono (by norm_num), fun τ k hk => le_trans (by norm_num) (h2 τ k hk), fun j τ k hk => ?_⟩
  have a := h3 τ k hk
  have b := h2 τ k hk
  have c : -2 ≤ gap (FlagTan.kap Dw τ) k := by
    simp only [gap, dite_eq_left hk, FlagTan.kap]
    split_ifs <;> push_cast <;> omega
  simp only [gap, dite_eq_left hk, WtPar.wt, WtPar.uc, Pi.add_apply, Pi.smul_apply] at a b c ⊢
  simp only [nsmul_eq_mul]
  have e1 := mul_nonneg (Int.natCast_nonneg (FlagTan.dimFlag Dw)) (le_trans (by norm_num) a)
  have e2 := mul_nonneg (Int.natCast_nonneg j) (le_trans (by norm_num) a)
  nlinarith

theorem two_le_dimFlag (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) (hf : 2 < Module.finrank ℚ E / 2) : 2 ≤ FlagTan.dimFlag Dw := by
  unfold FlagTan.dimFlag
  have : 1 ≤ (Dw.p + Dw.q).choose 2 := Nat.choose_pos (by omega)
  nlinarith

end Weights

end GlobalTheory.CovTop.ShareRowsNef

end
