module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.ProjectiveLattices.IsThRule
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.DIV

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

abbrev Psi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : Type := {τ : E →+* ℂ // InPsi H τ}

instance instFintypePsi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : Fintype (Psi H) := Fintype.ofFinite _

def IsPartFam (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∀ (σ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult σ → a (σ, j) ≤ a (σ, i)

def part (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (σ : E →+* ℂ) (i : ℕ) : ℕ :=
  if i < Dw.mult σ then a (σ, i) else 0

theorem part_anti {Dw : Datum H} {a : (E →+* ℂ) × ℕ → ℕ} (ha : IsPartFam Dw a) (σ : E →+* ℂ) :
    Antitone (part Dw a σ) := by
  intro i j hij
  unfold part
  by_cases hj : j < Dw.mult σ
  · rw [ite_eq_left hj, ite_eq_left (lt_of_le_of_lt hij hj)]
    exact ha σ i j hij hj
  · rw [ite_eq_right hj]
    exact Nat.zero_le _

def lamP (Dw : Datum H) (n : ℕ) {a : (E →+* ℂ) × ℕ → ℕ} (ha : IsPartFam Dw a) (d : Psi H → ℤ) (τ : Psi H) :
    DomWeight n where
  w i := (part Dw a τ.1 i.val : ℤ) - (part Dw a (ComplexEmbedding.conjugate τ.1) (Fin.rev i).val : ℤ) + d τ
  anti := by
    intro i j hij
    have h1 := part_anti ha τ.1 (show i.val ≤ j.val from hij)
    have h2 := part_anti ha (ComplexEmbedding.conjugate τ.1)
      (show (Fin.rev j).val ≤ (Fin.rev i).val from Fin.rev_le_rev.mpr hij)
    simp only
    omega

variable {l : Level H} (Dw : Datum H) (c : Coeff l) (n : ℕ)

def embPsi : Psi H → E →+* c.F := fun τ => embF c τ.1

variable {a : (E →+* ℂ) × ℕ → ℕ} (ha : IsPartFam Dw a) (d : Psi H → ℤ)

abbrev CoefSp : Type := VV c.F (lamP Dw n ha d)

def coefRep : GL (Fin n) E →* Module.End c.F (CoefSp Dw c n ha d) :=
  rhoVr (embPsi c) (lamP Dw n ha d)


open Classical in
def coefAct (γ : Matrix (Fin n) (Fin n) E) : CoefSp Dw c n ha d →ₗ[c.F] CoefSp Dw c n ha d :=
  if h : IsUnit γ then coefRep Dw c n ha d h.unit else 0

def vacChar (γ : Matrix (Fin n) (Fin n) E) : c.F := ∏ τ : Psi H, embPsi c τ γ.det ^ (-(d τ))

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by omega)


end GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights
