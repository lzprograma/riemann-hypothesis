module

public import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.TableDegreeElevenProduct
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundOfConditionsWithErrorForFrames
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.LatticeGeometry.InstAddCommSemigroupWt
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AMiEqAMinusQ
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DescentConstants, Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities

-- ===== clump member: Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DescentConstants =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DescentConstants", "h": "module\n\npublic import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.TableDegreeElevenProduct\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants

open Formalism.BasicNotions Formalism.MainNotions Finset

def cOne : ℝ := 8

def cThree : ℝ := 94

def cSix : ℝ := 32

def ceilEight (n : ℕ) : ℕ := 8 * ((n + 7) / 8)

section Numbers

variable (D : D7) (L : SizeData₂ D)

def lrd : ℝ := Real.log D.host.rdE

def pp (j : ℕ) : ℕ := (D.R.sigW j).1

def qq (j : ℕ) : ℕ := (D.R.sigW j).2

def dY : ℝ := (placeRankTwoOne.dimY D : ℝ)

def dX (j : ℕ) : ℕ := D.R.f * pp D j * qq D j

def cTw (j : ℕ) : ℕ := ceilEight (max (D.R.r + (dX D j + 1).choose 2 + 2) (8 * D.R.f * D.R.r + 4))

def nCol (j : ℕ) : ℕ :=
  ceilEight (max (D.R.f * (pp D j * (pp D j + 1) + qq D j * (qq D j + 1))) (8 * D.R.f * D.R.r + 4))

def bigR : ℝ := D.host.rdE ^ 7

def degStar : ℝ := 7 * (D.R.f : ℝ) * D.R.k * L.sc.b

def expQ : ℕ := sInf {c : ℕ | bigR D ^ 7 * degStar D L ^ 2 ≤ (3 : ℝ) ^ (2 * c)}

def levQ : ℕ := 3 ^ (2 * expQ D L)

def expC : ℕ := sInf {c : ℕ | bigR D ^ 8 * degStar D L ^ 2 ≤ (3 : ℝ) ^ c ∧ max 4 (2 * expQ D L) ≤ c}

def levDeep : ℕ := D.host.g 0 * D.host.g 1 * (3 ^ expC D L * 5 ^ expC D L)

def shareW (g : ℕ) : ℝ :=
  3 * (D.R.f : ℝ) / g + 23 * D.R.f * Real.log g * (g : ℝ) ^ (-(1 : ℝ) / 2) +
    2 * D.R.f * D.R.m * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log D.R.r) / ((g : ℝ) - 1)) +
    (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f + Real.exp (-(D.R.f : ℝ) / (5 * Real.log D.R.r))

def del : ℝ := shareW D (D.host.g 0) + shareW D (D.host.g 1)

def kap (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := if h : i < D.R.r then DV.kapW D j τ ⟨i, h⟩ else 0

def wAn (j : ℕ) (τ : D.what₂.Tau) : ℤ := kap D j τ (D.R.k - 2)

def uAn (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := kap D j τ i - wAn D j τ

def nrm (v : ℕ → ℤ) : ℝ := ∑ i ∈ range D.R.r, |(v i : ℝ)|

def nKap (j : ℕ) : ℝ := ∑ τ, nrm D (kap D j τ)

def deW (j i : ℕ) : ℤ := if i < pp D j then 0 else -1

def canW (j i : ℕ) : ℤ :=
  if i < pp D j then (qq D j : ℤ) - pp D j + 1 + 2 * i else -(pp D j : ℤ) - qq D j + 1 + 2 * ((i : ℤ) - pp D j)

def aW (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uAn D j τ i - (cTw D j : ℤ) * deW D j i - canW D j i

def degW (v : D.what₂.Tau → ℕ → ℤ) : ℝ :=
  ∏ τ, ∏ l ∈ range D.R.r, ∏ i ∈ range l, ((v τ i : ℝ) - v τ l)

def shift : ℝ := (D.R.nV : ℝ) / 2 * D.R.f * D.R.r * (Real.log (2 * Real.pi) / 2 + lrd D)

end Numbers

section Run

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P)

def ppTsq : ℝ :=
  max (1.2e9 * (D.R.r : ℝ) ^ 2)
    (max (448 * cOne * Q.PP * D.R.f * D.R.m) (32 * cThree * cSix * Q.PP * D.R.f * D.R.m))

def tN : ℕ := ⌈ppTsq Q * dY D ^ 2 * D.R.k / D.R.m⌉₊

def tR : ℝ := (tN Q : ℝ)

def gapOne (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ :=
  (aW D j τ i - aW D j τ (i + 1)) / ((tN Q + placeRankTwoOne.dimY D + 1 : ℕ) : ℤ)

def uOne (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ :=
  (∑ l ∈ Ico i (D.R.k - 2), gapOne Q j τ l) - ∑ l ∈ Ico (D.R.k - 2) i, gapOne Q j τ l

def uPr (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := uOne Q j τ i - 3 * (D.R.r : ℤ) * deW D j i

def rhoB (j : ℕ) : ℝ := 1 - degW D (uPr Q j) / degW D (uOne Q j)

def zed (j : ℕ) : ℝ := 7 * (dY D ^ 2 / tR Q + dY D * rhoB Q j)

def numBase (j : ℕ) : OT.Num where
  D := placeRankTwoOne.dimY D
  DX := dX D j
  f := D.R.f
  r := D.R.r
  m := D.R.m
  L := L.sc.L
  j := qq D j
  nW := Q.nWn
  Np := nCol D j
  lrd := lrd D
  LL := |L.logDerivativeAtOne|
  lM := Real.log (levDeep D L)
  lg := Real.log ((D.host.g 0 : ℝ) * D.host.g 1)
  lg1 := max (Real.log (D.host.g 0)) (Real.log (D.host.g 1))
  lp := max (Real.log D.host.pde) (Real.log D.host.pde')
  ld := Real.log D.host.d
  l4 := Real.log (max (4 * (D.R.n : ℝ) ^ 2) ((D.host.QS : ℝ) ^ 2 / 4) * D.host.q * D.host.d)
  l2q := Real.log ((D.host.QS : ℝ) * D.host.q * D.host.d)
  lx := Real.log L.sc.x
  llx := Real.log (Real.log L.sc.x)
  n := D.R.nV
  w := L.sc.b ^ 2
  a := nKap D j - (D.R.f : ℝ) * D.R.r * D.R.nV / 2
  ka := nKap D j
  u1 := ∑ τ, nrm D (uOne Q j τ)
  DF := degStar D L
  DFs := degStar D L
  RTc := bigR D * tR Q * (bigR D * Q.PP * degStar D L ^ 2 / levQ D L)
  lh := 0
  lNc := 0
  lpi := 0
  lmu := 0
  lmu1 := 0
  V := 0
  hb := 0
  logGenusConstant := 0
  dS := 0
  rS := 0
  dP := 0
  rP := 0
  lNA := 0
  Om := 0
  nu := 0
  lc := 0
  leE := 0
  ln0 := 0
  c1 := 0
  sc1 := 0
  G1 := 0
  CL := 0
  lR := 0
  rho := 0
  dp := 0
  gC := 0

def numAt (j : ℕ) : OT.Num := (numBase Q j).hat

end Run

end GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DescentConstants =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities", "h": "module\n\npublic import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundOfConditionsWithErrorForFrames\npublic import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DescentConstants\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal\npublic import Formalism.LocalToGlobal.IndefiniteReal.FWExist\npublic import Formalism.LocalToGlobal.LatticeGeometry.InstAddCommSemigroupWt\npublic import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AMiEqAMinusQ\nimport Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Finset Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P)

section Weights


variable (D) in
def kapMinus (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℤ := kap D j τ i - (cTw D j : ℤ) * deW D j i


variable (D) in
def twW (j : ℕ) (_ : D.what₂.Tau) (i : ℕ) : ℤ := (cTw D j : ℤ) * deW D j i

end Weights

section Numbers

variable (D L) in
def badPrimes (B : ℝ) : Finset ℕ :=
  (range (⌊B⌋₊ + 1)).filter Nat.Prime ∪ (2 * (discr D.host.E).natAbs * levDeep D L).primeFactors


def cA (j : ℕ) : ℝ := 26 * (26 * dY D ^ 2 + 2 * zed Q j * tR Q)

def cG (j : ℕ) : ℝ := (dY D + 1) * ((numAt Q j).o + (numAt Q j).B7 + 1) / 2 + 1

end Numbers

section Transport

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.CompHt
open Formalism.L2.Pj hiding kap

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E}


open Classical in
def toWt (Dw : Datum H) (v : D.what₂.Tau → ℕ → ℤ) : Weight Dw :=
  fun τ i => ∑ t, if τ.1 = DV.tauEmb D t then v t i else 0

variable {Dw : Datum H}

def psiOf {T : Par D} (h : T.PinHost) (t : D.what₂.Tau) : Psi T.H := ⟨DV.tauEmb D t, h.2.2.2 t⟩

theorem psiOf_bijective {T : Par D} (h : T.Pins) : Function.Bijective (psiOf h.1) := by
  have hj : InR D 1 := ⟨le_rfl, le_trans one_le_two D.R.two_le_m⟩
  refine ⟨fun s t e => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val e), fun τ => ?_⟩
  obtain ⟨t, ht⟩ := ((GlobalTheory.WeightExponents.weight_exponents D T h 1 hj
    (WeightAlgebra.wscalar D 1 0 Even.zero)).2.2.1 τ.1).1 τ.2
  exact ⟨t, Subtype.ext ht.symm⟩

variable {T : Par D} {j : ℕ}

theorem sig_eq (h : T.Pins) (hj : InR D j) :
    (T.Dw j).p = pp D j ∧ (T.Dw j).q = qq D j ∧ (T.Dw j).p + (T.Dw j).q = D.R.r := by
  obtain ⟨h1, h2, -⟩ := h.2.2.2 j hj
  refine ⟨h1, h2, ?_⟩
  have := D.R.m_add_three_le_k
  have := hj.1
  have := hj.2
  rw [h1, h2]
  simp only [Ranks.sigW, Ranks.r]; omega

theorem dimFlag_eq (h : T.Pins) (hj : InR D j) : dimFlag (T.Dw j) = placeRankTwoOne.dimY D := by
  rw [dimFlag, Formalism.DegreeFormula.dimFl, (sig_eq h hj).2.2, ← Fintype.card_of_bijective (psiOf_bijective h), D.what₂.card_Tau,
    placeRankTwoOne.dimY, Nat.choose_two_right]


variable (D) in
def thetaExp (Dw : Datum H) (v : D.what₂.Tau → ℕ → ℤ) : WTZ D.host.E := wtOf Dw (toWt Dw v) ((D.R.nV / 2 : ℕ) : ℤ)


variable (D) in
def plainExp (Dw : Datum H) (v : D.what₂.Tau → ℕ → ℤ) : WTZ D.host.E := wtOf Dw (toWt Dw v) 0

end Transport

end GlobalTheory.SlopeRec
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities =====
