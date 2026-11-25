module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulNonsingInvCancelRightGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebra
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcrOperatorsThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTraceStatement
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtWeilRepRealOneParamAdelicPoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationOneParameterGenerator
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PderivComm, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunctionStatement, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealLieAlgebraActsByFockOperatorsUpToScalars, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealLieAlgebraActsByFockOperatorsUpToScalarsStatement, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAdd, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAddStatement, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealDerivativeFockVectorsAll

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PderivComm =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PderivComm", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators\npublic import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Etale.Weakly\nimport Mathlib.RingTheory.Finiteness.ModuleFinitePresentation\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.BitVec\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.WeilReal.QuadAlg

open Matrix MvPolynomial
open scoped ComplexConjugate

section Abstract

theorem pderiv_comm' {σ : Type} (i j : σ) (p : MvPolynomial σ ℂ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p s hp =>
    simp only [Derivation.leibniz, pderiv_X, map_add (f := _), smul_eq_mul, hp]
    simp only [Pi.single_apply]
    split_ifs <;> simp <;> ring

variable {κ σ : Type} [Fintype κ] [DecidableEq κ] [DecidableEq σ]

def wOp (e : κ → σ) (p : κ → Prop) [DecidablePred p] (k : κ) (Q : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  if p k then X (e k) * Q else -pderiv (e k) Q

def vOp (e : κ → σ) (p : κ → Prop) [DecidablePred p] (k : κ) (Q : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  if p k then pderiv (e k) Q else X (e k) * Q

def fc (p : κ → Prop) [DecidablePred p] (k : κ) (c : ℂ) : ℂ := if p k then c else conj c

def mA (p : κ → Prop) [DecidablePred p] (A : Matrix κ κ ℂ) (k l : κ) : ℂ :=
  if (p k ↔ p l) then fc p k (A k l) else 0

def nA (p : κ → Prop) [DecidablePred p] (A : Matrix κ κ ℂ) (k l : κ) : ℂ :=
  if (p k ↔ p l) then 0 else fc p k (A k l)

def gT (e : κ → σ) (p : κ → Prop) [DecidablePred p] (A : Matrix κ κ ℂ) (P : MvPolynomial σ ℂ) (k l : κ) :
    MvPolynomial σ ℂ :=
  C (mA p A k l) * X (e k) * pderiv (e l) P + C (nA p A k l / 2) * X (e k) * X (e l) * P -
    C (conj (nA p A k l) / 2) * pderiv (e k) (pderiv (e l) P)

theorem pair_eq (e : κ → σ) (he : Function.Injective e) (p : κ → Prop) [DecidablePred p] (A : Matrix κ κ ℂ)
    (hA : ∀ k l, conj (A k l) = (if (p k ↔ p l) then -A l k else A l k)) (P : MvPolynomial σ ℂ) (k l : κ) :
    C (A k l) * wOp e p k (vOp e p l P) + C (A l k) * wOp e p l (vOp e p k P) =
      gT e p A P k l + gT e p A P l k -
        (if k = l ∧ ¬ p k then C (2 * A k k) * P else 0) := by
  have hd : ∀ (a b : κ) (Q : MvPolynomial σ ℂ), pderiv (e a) (pderiv (e b) Q) = pderiv (e b) (pderiv (e a) Q) :=
    fun a b Q => pderiv_comm' _ _ _
  have hx : ∀ (a b : κ) (Q : MvPolynomial σ ℂ), pderiv (e a) (X (e b) * Q) =
      X (e b) * pderiv (e a) Q + (if a = b then Q else 0) := fun a b Q => by
    rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
    simp only [Pi.single_apply, he.eq_iff]
    by_cases h : a = b
    · simp [h]
    · simp [h, Ne.symm h]
  have hkl := hA k l
  have hlk := hA l k
  have h2 : ∀ c : ℂ, C c = C (c / 2) + (C (c / 2) : MvPolynomial σ ℂ) := fun c => by
    rw [← C_add, add_halves]
  have h2' : ∀ c : ℂ, C (2 * c) = C c + (C c : MvPolynomial σ ℂ) := fun c => by
    rw [← C_add, two_mul]
  have wp : ∀ a, p a → ∀ Q, wOp e p a Q = X (e a) * Q := fun a h Q => ite_eq_left h
  have wn : ∀ a, ¬ p a → ∀ Q, wOp e p a Q = -pderiv (e a) Q := fun a h Q => ite_eq_right h
  have vp : ∀ a, p a → ∀ Q, vOp e p a Q = pderiv (e a) Q := fun a h Q => ite_eq_left h
  have vn : ∀ a, ¬ p a → ∀ Q, vOp e p a Q = X (e a) * Q := fun a h Q => ite_eq_right h
  have fp : ∀ a, p a → ∀ c, fc p a c = c := fun a h c => ite_eq_left h
  have fn : ∀ a, ¬ p a → ∀ c, fc p a c = conj c := fun a h c => ite_eq_right h
  have ms : ∀ a b, (p a ↔ p b) → mA p A a b = fc p a (A a b) := fun a b h => ite_eq_left h
  have md : ∀ a b, ¬ (p a ↔ p b) → mA p A a b = 0 := fun a b h => ite_eq_right h
  have ns : ∀ a b, (p a ↔ p b) → nA p A a b = 0 := fun a b h => ite_eq_left h
  have nd : ∀ a b, ¬ (p a ↔ p b) → nA p A a b = fc p a (A a b) := fun a b h => ite_eq_right h
  by_cases hk : p k <;> by_cases hl : p l
  · have hn : ¬ (k = l ∧ ¬ p k) := fun h => h.2 hk
    have e1 : (p k ↔ p l) := by simp [hk, hl]
    rw [ite_eq_right hn, wp k hk, wp l hl, vp k hk, vp l hl]
    simp only [gT, ms k l e1, ms l k e1.symm, ns k l e1, ns l k e1.symm, fp k hk, fp l hl, zero_div, map_zero]
    ring
  · have hne : k ≠ l := fun h => hl (h ▸ hk)
    have hn : ¬ (k = l ∧ ¬ p k) := fun h => hne h.1
    have e1 : ¬ (p k ↔ p l) := by simp [hk, hl]
    have e2 : ¬ (p l ↔ p k) := by simp [hk, hl]
    rw [ite_eq_right e1] at hkl
    rw [ite_eq_right e2] at hlk
    rw [ite_eq_right hn, wp k hk, wn l hl, vp k hk, vn l hl]
    simp only [gT, md k l e1, md l k e2, nd k l e1, nd l k e2, fp k hk, fn l hl, hlk, hkl, map_zero]
    rw [h2 (A k l), h2 (A l k), hd l k]
    ring
  · have hne : k ≠ l := fun h => hk (h ▸ hl)
    have hn : ¬ (k = l ∧ ¬ p k) := fun h => hne h.1
    have e1 : ¬ (p k ↔ p l) := by simp [hk, hl]
    have e2 : ¬ (p l ↔ p k) := by simp [hk, hl]
    rw [ite_eq_right e1] at hkl
    rw [ite_eq_right e2] at hlk
    rw [ite_eq_right hn, wn k hk, wp l hl, vn k hk, vp l hl]
    simp only [gT, md k l e1, md l k e2, nd k l e1, nd l k e2, fn k hk, fp l hl, hlk, hkl, map_zero]
    rw [h2 (A k l), h2 (A l k), hd l k]
    ring
  · have e1 : (p k ↔ p l) := by simp [hk, hl]
    have e2 : (p l ↔ p k) := by simp [hk, hl]
    rw [ite_eq_left e1] at hkl
    rw [ite_eq_left e2] at hlk
    rw [wn k hk, wn l hl, vn k hk, vn l hl, hx, hx]
    simp only [gT, ms k l e1, ms l k e2, ns k l e1, ns l k e2, fn k hk, fn l hl, hlk, hkl, map_zero, zero_div,
      map_neg]
    by_cases h : k = l
    · subst h
      simp only [ite_true, true_and, ite_eq_left hk]
      rw [h2' (A k k)]
      ring
    · have h' : l ≠ k := Ne.symm h
      rw [ite_eq_right (fun hh : k = l ∧ ¬ p k => h hh.1), ite_eq_right h, ite_eq_right h']
      ring

theorem sum_eq (e : κ → σ) (he : Function.Injective e) (p : κ → Prop) [DecidablePred p] (A : Matrix κ κ ℂ)
    (hA : ∀ k l, conj (A k l) = (if (p k ↔ p l) then -A l k else A l k)) (P : MvPolynomial σ ℂ) :
    ∑ k, ∑ l, C (A k l) * wOp e p k (vOp e p l P) =
      ∑ k, ∑ l, gT e p A P k l - ∑ k, (if p k then 0 else C (A k k) * P) := by
  set S := ∑ k, ∑ l, C (A k l) * wOp e p k (vOp e p l P) with hS
  set G := ∑ k, ∑ l, gT e p A P k l with hG
  set R := ∑ k, (if p k then 0 else C (A k k) * P) with hR
  have h1 : S + S = (G + G) - (R + R) := by
    have e1 : S + S = ∑ k, ∑ l, (C (A k l) * wOp e p k (vOp e p l P) + C (A l k) * wOp e p l (vOp e p k P)) := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun k l => C (A l k) * wOp e p l (vOp e p k P))]
    have e2 : G + G = ∑ k, ∑ l, (gT e p A P k l + gT e p A P l k) := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun k l => gT e p A P l k)]
    have e3 : R + R = ∑ k, ∑ l, (if k = l ∧ ¬ p k then C (2 * A k k) * P else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : p k
      · simp [hk]
      · simp only [hk, ite_false, not_false_eq_true, and_true, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [two_mul, C_add, add_mul]
    rw [e1, e2, e3, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => pair_eq e he p A hA P k l
  have h2 : (2 : ℂ) • S = (2 : ℂ) • (G - R) := by
    rw [two_smul, two_smul, h1]
    abel
  exact smul_right_injective _ (two_ne_zero (α := ℂ)) h2

end Abstract

section Concrete

open Formalism.BasicNotions Formalism.IndefR.Datum Formalism.IndefR.Fock.Sk GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

def sgB {k : ℕ} (p : ℕ) (a : Fin k) : Bool := decide ((a : ℕ) < p)

theorem sgn_sq (e : Bool) : sgn e * sgn e = 1 := by cases e <;> simp [sgn]

theorem onb_facts {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    IsUnit B.det ∧ Bᴴ * G * B = Formalism.REAL.Jm (sgB p) ∧ s * B = B * Formalism.REAL.Jm (sgB p) := by
  obtain ⟨ε, h1, h2, h3⟩ := h
  have e : (diagonal fun a => (ε a : ℂ)) = Formalism.REAL.Jm (sgB p) := by
    rw [GlobalTheory.LieFock.Jm_eq]
    congr 1
    funext a
    rcases h1 a with ⟨h, h'⟩ | ⟨h, h'⟩
    · simp [h, h', sgB, sgn]
    · simp [h, sgB, sgn, not_lt.2 h']
  rw [e] at h2 h3
  refine ⟨?_, h2, h3⟩
  have hJ : Formalism.REAL.Jm (sgB (k := k) p) * Formalism.REAL.Jm (sgB p) = 1 := by
    simp only [GlobalTheory.LieFock.Jm_eq, diagonal_mul_diagonal, sgn_sq, diagonal_one]
  refine Matrix.isUnit_det_of_left_inverse (B := Formalism.REAL.Jm (sgB p) * (Bᴴ * G)) ?_
  rw [Matrix.mul_assoc, h2, hJ]

theorem lie_entry' {k : ℕ} {G B X : Matrix (Fin k) (Fin k) ℂ} {ε : Fin k → Bool} (hB : IsUnit B.det)
    (hG : Bᴴ * G * B = Formalism.REAL.Jm ε) (hX : Xᴴ * G + G * X = 0) (a b : Fin k) :
    conj ((B⁻¹ * X * B) a b) = -(sgn (ε a) * sgn (ε b)) * (B⁻¹ * X * B) b a := by
  have hBi : IsUnit B⁻¹.det := isUnit_nonsing_inv_det B hB
  have hGi : (B⁻¹)ᴴ * Formalism.REAL.Jm ε * B⁻¹ = G := by
    rw [← hG, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hB,
      conjTranspose_one, Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv _ hB, Matrix.mul_one]
  simpa [nonsing_inv_nonsing_inv _ hB] using GlobalTheory.LieFock.lie_entry hBi hGi hX a b

variable {m n : ℕ}

def aK (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  fun k l => (Y * Matrix.single l.1 l.2 (1 : ℂ) - Matrix.single l.1 l.2 (1 : ℂ) * X) k.1 k.2

theorem aK_apply (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) (k l : Fin m × Fin n) :
    aK X Y k l = (if k.2 = l.2 then Y k.1 l.1 else 0) - (if k.1 = l.1 then X l.2 k.2 else 0) := by
  by_cases h1 : k.2 = l.2 <;> by_cases h2 : k.1 = l.1 <;>
    simp [aK, Matrix.mul_apply, Matrix.single_apply, eq_comm, h1, h2]

def pp (pS pT : ℕ) (k : Fin m × Fin n) : Prop := PosF (m := m) (n := n) pS pT k.1 k.2

instance (pS pT : ℕ) : DecidablePred (pp (m := m) (n := n) pS pT) :=
  fun k => inferInstanceAs (Decidable (PosF pS pT k.1 k.2))

def sL (pS pT : ℕ) (k : Fin m × Fin n) : ℂ := sgn (sgB pT k.1) * sgn (sgB pS k.2)

theorem sL_eq (pS pT : ℕ) (k : Fin m × Fin n) : sL pS pT k = if pp pS pT k then 1 else -1 := by
  simp only [sL, sgB, pp, PosF, sgn]
  by_cases h1 : (k.1 : ℕ) < pT <;> by_cases h2 : (k.2 : ℕ) < pS <;> simp [h1, h2]

theorem sL_mul (pS pT : ℕ) (k l : Fin m × Fin n) :
    sL pS pT k * sL pS pT l = if (pp pS pT k ↔ pp pS pT l) then 1 else -1 := by
  rw [sL_eq, sL_eq]
  by_cases h1 : pp pS pT k <;> by_cases h2 : pp pS pT l <;> simp [h1, h2]

theorem aK_conj {X : Matrix (Fin n) (Fin n) ℂ} {Y : Matrix (Fin m) (Fin m) ℂ} {pS pT : ℕ}
    (hX : ∀ a b, conj (X a b) = -(sgn (sgB pS a) * sgn (sgB pS b)) * X b a)
    (hY : ∀ a b, conj (Y a b) = -(sgn (sgB pT a) * sgn (sgB pT b)) * Y b a) (k l : Fin m × Fin n) :
    conj (aK X Y k l) = if (pp pS pT k ↔ pp pS pT l) then -aK X Y l k else aK X Y l k := by
  have e : conj (aK X Y k l) = -(sL pS pT k * sL pS pT l) * aK X Y l k := by
    rw [aK_apply, aK_apply, map_sub]
    obtain ⟨i, j⟩ := k
    obtain ⟨i', j'⟩ := l
    simp only [sL]
    have ha := fun i => sgn_sq (sgB pT (i : Fin m))
    have hb := fun j => sgn_sq (sgB pS (j : Fin n))
    by_cases h1 : j = j' <;> by_cases h2 : i = i'
    · subst h1 h2
      simp only [ite_true, hX, hY]
      linear_combination (-(X j j) * sgn (sgB pS j) * sgn (sgB pS j)) * ha i +
        (sgn (sgB pT i) * sgn (sgB pT i) * Y i i) * hb j
    · subst h1
      have h2' : i' ≠ i := Ne.symm h2
      simp only [ite_true, ite_eq_right h2, ite_eq_right h2', map_zero, sub_zero, hY]
      linear_combination (sgn (sgB pT i) * sgn (sgB pT i') * Y i' i) * hb j
    · subst h2
      have h1' : j' ≠ j := Ne.symm h1
      simp only [ite_true, ite_eq_right h1, ite_eq_right h1', map_zero, zero_sub, hX]
      linear_combination (-(sgn (sgB pS j) * sgn (sgB pS j') * X j j')) * ha i
    · have h1' : j' ≠ j := Ne.symm h1
      have h2' : i' ≠ i := Ne.symm h2
      simp [h1, h2, h1', h2']
  rw [e, sL_mul]
  split_ifs <;> simp

section Coef

variable {sS BS XS : Matrix (Fin n) (Fin n) ℂ} {sT BT XT : Matrix (Fin m) (Fin m) ℂ} {pS pT : ℕ}

theorem cplxO_conj (hS : IsUnit BS.det) (hsS : sS * BS = BS * Formalism.REAL.Jm (sgB pS))
    (hsT : sT * BT = BT * Formalism.REAL.Jm (sgB pT)) (W : Matrix (Fin m) (Fin n) ℂ) :
    cplxO sS sT (BT * W * BS⁻¹) = BT * (Complex.I • ((Formalism.REAL.Jm (sgB pT) : Matrix (Fin m) (Fin m) ℂ) * W *
      (Formalism.REAL.Jm (sgB pS) : Matrix (Fin n) (Fin n) ℂ))) * BS⁻¹ := by
  have h : BS⁻¹ * sS = Formalism.REAL.Jm (sgB pS) * BS⁻¹ := by
    have e : sS = BS * Formalism.REAL.Jm (sgB pS) * BS⁻¹ := by rw [← hsS, mul_nonsing_inv_cancel_right _ _ hS]
    rw [e, Matrix.mul_assoc BS, nonsing_inv_mul_cancel_left _ _ hS]
  have e : sT * (BT * W * BS⁻¹) * sS = BT * (Formalism.REAL.Jm (sgB (k := m) pT) * W * Formalism.REAL.Jm (sgB (k := n) pS)) * BS⁻¹ := by
    calc _ = (sT * BT) * W * (BS⁻¹ * sS) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hsT, h]; simp only [Matrix.mul_assoc]
  rw [cplxO, e, Matrix.mul_smul, Matrix.smul_mul]

theorem adX_conj (hS : IsUnit BS.det) (hT : IsUnit BT.det) (W : Matrix (Fin m) (Fin n) ℂ) :
    adX XS XT (BT * W * BS⁻¹) = BT * ((BT⁻¹ * XT * BT) * W - W * (BS⁻¹ * XS * BS)) * BS⁻¹ := by
  have h1 : BT * ((BT⁻¹ * XT * BT) * W) * BS⁻¹ = XT * (BT * W * BS⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hT]
  have h2 : BT * (W * (BS⁻¹ * XS * BS)) * BS⁻¹ = BT * W * BS⁻¹ * XS := by
    simp only [Matrix.mul_assoc]
    rw [mul_nonsing_inv _ hS, Matrix.mul_one]
  rw [adX, Matrix.mul_sub, Matrix.sub_mul, h1, h2]

theorem fCoord_conj (hS : IsUnit BS.det) (hT : IsUnit BT.det) (W : Matrix (Fin m) (Fin n) ℂ) (k : Fin m × Fin n) :
    fCoord BS BT pS pT (BT * W * BS⁻¹) k = fc (pp pS pT) k (W k.1 k.2) := by
  have e : BT⁻¹ * (BT * W * BS⁻¹) * BS = W := by
    rw [Matrix.mul_assoc BT, nonsing_inv_mul_cancel_left _ _ hT, nonsing_inv_mul_cancel_right _ _ hS]
  simp only [fCoord, fc, pp, e]
  rfl

theorem Jm_entry {a b : ℕ} (ε : Fin a → Bool) (ε' : Fin b → Bool) (W : Matrix (Fin a) (Fin b) ℂ) (i : Fin a) (j : Fin b) :
    (Formalism.REAL.Jm ε * W * Formalism.REAL.Jm ε') i j = sgn (ε i) * W i j * sgn (ε' j) := by
  rw [GlobalTheory.LieFock.Jm_eq, GlobalTheory.LieFock.Jm_eq, mul_diagonal, diagonal_mul]

theorem part_entry (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (k l : Fin m × Fin n) :
    ((1 / 2 : ℂ) • ((Y * Matrix.single l.1 l.2 (1 : ℂ) - Matrix.single l.1 l.2 (1 : ℂ) * X) + c •
      (Complex.I • ((Formalism.REAL.Jm (sgB pT) : Matrix (Fin m) (Fin m) ℂ) *
        (Y * (Complex.I • ((Formalism.REAL.Jm (sgB pT) : Matrix (Fin m) (Fin m) ℂ) * Matrix.single l.1 l.2 (1 : ℂ) *
          (Formalism.REAL.Jm (sgB pS) : Matrix (Fin n) (Fin n) ℂ))) -
        (Complex.I • ((Formalism.REAL.Jm (sgB pT) : Matrix (Fin m) (Fin m) ℂ) * Matrix.single l.1 l.2 (1 : ℂ) *
          (Formalism.REAL.Jm (sgB pS) : Matrix (Fin n) (Fin n) ℂ))) * X) *
        (Formalism.REAL.Jm (sgB pS) : Matrix (Fin n) (Fin n) ℂ))))) k.1 k.2 =
      (1 / 2 : ℂ) * (1 - c * (sL pS pT k * sL pS pT l)) * aK X Y k l := by
  have e1 : (Formalism.REAL.Jm (sgB pT) : Matrix (Fin m) (Fin m) ℂ) * Matrix.single l.1 l.2 (1 : ℂ) *
      (Formalism.REAL.Jm (sgB pS) : Matrix (Fin n) (Fin n) ℂ) = sL pS pT l • Matrix.single l.1 l.2 (1 : ℂ) := by
    ext a b
    rw [Jm_entry, Matrix.smul_apply, Matrix.single_apply, sL, smul_eq_mul]
    by_cases h : l.1 = a ∧ l.2 = b
    · obtain ⟨h1, h2⟩ := h
      subst h1 h2
      simp
    · simp [h]
  rw [e1]
  have e2 : Y * (Complex.I • sL pS pT l • Matrix.single l.1 l.2 (1 : ℂ)) -
      (Complex.I • sL pS pT l • Matrix.single l.1 l.2 (1 : ℂ)) * X =
      (Complex.I * sL pS pT l) • (Y * Matrix.single l.1 l.2 (1 : ℂ) - Matrix.single l.1 l.2 (1 : ℂ) * X) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_smul]
  have e3 : ∀ (w : ℂ) (F : Matrix (Fin m) (Fin n) ℂ), ((Formalism.REAL.Jm (sgB pT) : Matrix (Fin m) (Fin m) ℂ) * (w • F) *
      (Formalism.REAL.Jm (sgB pS) : Matrix (Fin n) (Fin n) ℂ)) k.1 k.2 =
      w * (sgn (sgB pT k.1) * F k.1 k.2 * sgn (sgB pS k.2)) := fun w F => by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Jm_entry, smul_eq_mul]
  rw [e2, Matrix.smul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, e3]
  change (1 / 2 : ℂ) • (aK X Y k l + c • Complex.I • (Complex.I * sL pS pT l *
    (sgn (sgB pT k.1) * aK X Y k l * sgn (sgB pS k.2)))) = _
  simp only [smul_eq_mul, sL]
  linear_combination ((1 / 2 : ℂ) * c * (sgn (sgB pT l.1) * sgn (sgB pS l.2)) * sgn (sgB pT k.1) * sgn (sgB pS k.2) *
    aK X Y k l) * Complex.I_sq

theorem fc_zero (p : Fin m × Fin n → Prop) [DecidablePred p] (k : Fin m × Fin n) : fc p k 0 = 0 := by
  simp [fc]

theorem mCoef_eq (hS : IsUnit BS.det) (hT : IsUnit BT.det) (hsS : sS * BS = BS * Formalism.REAL.Jm (sgB pS))
    (hsT : sT * BT = BT * Formalism.REAL.Jm (sgB pT)) (k l : Fin m × Fin n) :
    mCoef sS BS XS sT BT XT pS pT k l = mA (pp pS pT) (aK (BS⁻¹ * XS * BS) (BT⁻¹ * XT * BT)) k l := by
  have h := part_entry (pS := pS) (pT := pT) (BS⁻¹ * XS * BS) (BT⁻¹ * XT * BT) (-1) k l
  rw [sL_mul] at h
  have e : ∀ F J : Matrix (Fin m) (Fin n) ℂ, (1 / 2 : ℂ) • (BT * F * BS⁻¹ - BT * J * BS⁻¹) =
      BT * ((1 / 2 : ℂ) • (F + (-1 : ℂ) • J)) * BS⁻¹ := fun F J => by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, neg_smul, one_smul, Matrix.mul_neg,
      Matrix.neg_mul, sub_eq_add_neg]
  simp only [mCoef, unitMap, cplxO_conj hS hsS hsT, adX_conj hS hT]
  rw [e, fCoord_conj hS hT, h]
  by_cases hp : pp pS pT k ↔ pp pS pT l
  · rw [ite_eq_left hp, mA, ite_eq_left hp]
    congr 1
    ring
  · rw [ite_eq_right hp, mA, ite_eq_right hp, show (1 / 2 : ℂ) * (1 - -1 * -1) = 0 by ring, zero_mul, fc_zero]

theorem nCoef_eq (hS : IsUnit BS.det) (hT : IsUnit BT.det) (hsS : sS * BS = BS * Formalism.REAL.Jm (sgB pS))
    (hsT : sT * BT = BT * Formalism.REAL.Jm (sgB pT)) (k l : Fin m × Fin n) :
    nCoef sS BS XS sT BT XT pS pT k l = nA (pp pS pT) (aK (BS⁻¹ * XS * BS) (BT⁻¹ * XT * BT)) k l := by
  have h := part_entry (pS := pS) (pT := pT) (BS⁻¹ * XS * BS) (BT⁻¹ * XT * BT) 1 k l
  rw [sL_mul] at h
  have e : ∀ F J : Matrix (Fin m) (Fin n) ℂ, (1 / 2 : ℂ) • (BT * F * BS⁻¹ + BT * J * BS⁻¹) =
      BT * ((1 / 2 : ℂ) • (F + (1 : ℂ) • J)) * BS⁻¹ := fun F J => by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, one_smul]
  simp only [nCoef, unitMap, cplxO_conj hS hsS hsT, adX_conj hS hT]
  rw [e, fCoord_conj hS hT, h]
  by_cases hp : pp pS pT k ↔ pp pS pT l
  · rw [ite_eq_left hp, nA, ite_eq_left hp, show (1 / 2 : ℂ) * (1 - 1 * 1) = 0 by ring, zero_mul, fc_zero]
  · rw [ite_eq_right hp, nA, ite_eq_right hp]
    congr 1
    ring

end Coef

section Final

variable {D : D7} (τ : D.what₂.Tau) {sS BS XS GS : Matrix (Fin n) (Fin n) ℂ} {sT BT XT GT : Matrix (Fin m) (Fin m) ℂ}
  (pS pT : ℕ)

def eV (k : Fin m × Fin n) : FVar D m n := (τ, k.1, k.2)

theorem eV_inj : Function.Injective (eV (D := D) (m := m) (n := n) τ) := fun k l h => by
  simp only [eV, Prod.mk.injEq, true_and] at h
  exact Prod.ext h.1 h.2

def tT (P : MvPolynomial (FVar D m n) ℂ) (k l : Fin m × Fin n) : MvPolynomial (FVar D m n) ℂ :=
  wOp (eV τ) (pp pS pT) k (vOp (eV τ) (pp pS pT) l P)

theorem sg_iff (i : Fin m) (j : Fin n) : (sgB pT i = sgB pS j) ↔ pp pS pT (i, j) := by
  simp only [sgB, pp, PosF, decide_eq_decide]

theorem rai_eq (i : Fin m) (j : Fin n) (Q : MvPolynomial (FVar D m n) ℂ) :
    raiO τ (sgB pS) (sgB pT) i j Q = sgn (sgB pS j) • wOp (eV τ) (pp pS pT) (i, j) Q := by
  unfold raiO wOp
  by_cases h : pp pS pT (i, j)
  · rw [ite_eq_left ((sg_iff pS pT i j).2 h), ite_eq_left h]
    rfl
  · rw [ite_eq_right (fun e => h ((sg_iff pS pT i j).1 e)), ite_eq_right h]
    rfl

theorem low_eq (i : Fin m) (j : Fin n) (Q : MvPolynomial (FVar D m n) ℂ) :
    lowO τ (sgB pS) (sgB pT) i j Q = sgn (sgB pS j) • vOp (eV τ) (pp pS pT) (i, j) Q := by
  unfold lowO vOp
  by_cases h : pp pS pT (i, j)
  · rw [ite_eq_left ((sg_iff pS pT i j).2 h), ite_eq_left h]
    rfl
  · rw [ite_eq_right (fun e => h ((sg_iff pS pT i j).1 e)), ite_eq_right h]
    rfl

theorem fockT_apply (Y : Matrix (Fin m) (Fin m) ℂ) (P : MvPolynomial (FVar D m n) ℂ) :
    fockT τ (sgB pS) (sgB pT) Y P = ∑ i, ∑ l, ∑ j, C (Y i l) * tT τ pS pT P (i, j) (l, j) +
      (((n : ℂ) / 2) * Y.trace) • P := by
  have term : ∀ i l j, (raiO τ (sgB pS) (sgB pT) i j * lowO τ (sgB pS) (sgB pT) l j +
      if i = l then (1 / 2 : ℂ) • (1 : Module.End ℂ (Formalism.IndefR.Links.PolF D m n)) else 0) P =
      tT τ pS pT P (i, j) (l, j) + (if i = l then (1 / 2 : ℂ) else 0) • P := fun i l j => by
    rw [LinearMap.add_apply, Module.End.mul_apply, low_eq, map_smul, rai_eq, smul_smul, sgn_sq, one_smul]
    congr 1
    split_ifs <;> simp
  simp only [fockT, LinearMap.sum_apply, LinearMap.smul_apply, term]
  simp only [Finset.smul_sum, smul_add, Finset.sum_add_distrib, C_mul']
  congr 1
  simp only [smul_smul, ← Finset.sum_smul]
  congr 1
  simp [Matrix.trace, mul_ite, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem fockS_apply (Z : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (FVar D m n) ℂ) :
    fockS τ (sgB pS) (sgB pT) Z P = ∑ j, ∑ k, ∑ i, C (Z j k * (sgn (sgB pS j) * sgn (sgB pS k))) * tT τ pS pT P (i, j) (i, k) +
      (((m : ℂ) / 2) * Z.trace) • P := by
  have term : ∀ i j k, (raiO τ (sgB pS) (sgB pT) i j * lowO τ (sgB pS) (sgB pT) i k +
      if j = k then (1 / 2 : ℂ) • (1 : Module.End ℂ (Formalism.IndefR.Links.PolF D m n)) else 0) P =
      (sgn (sgB pS j) * sgn (sgB pS k)) • tT τ pS pT P (i, j) (i, k) + (if j = k then (1 / 2 : ℂ) else 0) • P := fun i j k => by
    rw [LinearMap.add_apply, Module.End.mul_apply, low_eq, map_smul, rai_eq, smul_smul, mul_comm (sgn (sgB pS k))]
    congr 1
    split_ifs <;> simp
  simp only [fockS, LinearMap.sum_apply, LinearMap.smul_apply, term]
  simp only [Finset.smul_sum, smul_add, Finset.sum_add_distrib, C_mul', smul_smul]
  congr 1
  simp only [← Finset.sum_smul]
  congr 1
  simp [Matrix.trace, mul_ite, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem sum_aK {R : Type} [CommRing R] (c : ℂ →+* R) (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ)
    (T : Fin m × Fin n → Fin m × Fin n → R) :
    ∑ k, ∑ l, c (aK X Y k l) * T k l =
      ∑ i, ∑ l, ∑ j, c (Y i l) * T (i, j) (l, j) - ∑ j, ∑ k, ∑ i, c (X k j) * T (i, j) (i, k) := by
  simp only [Fintype.sum_prod_type, aK_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [apply_ite c, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · have e : ∀ i j, ∑ i', ∑ j', c (if (i, j).1 = (i', j').1 then X (i', j').2 (i, j).2 else 0) * T (i, j) (i', j') =
        ∑ k, c (X k j) * T (i, j) (i, k) := fun i j => by
      rw [Finset.sum_eq_single i (fun b _ hb => Finset.sum_eq_zero fun j' _ => by simp [Ne.symm hb]) (by simp)]
      simp
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]

theorem fock_eq_quad (hS : IsONBasis GS sS BS pS) (hT : IsONBasis GT sT BT pT) (hX : XSᴴ * GS + GS * XS = 0)
    (hY : XTᴴ * GT + GT * XT = 0) (P : MvPolynomial (FVar D m n) ℂ) :
    fockS τ (sgB pS) (sgB pT) ((BS⁻¹ * XS * BS).map (starRingEnd ℂ)) P + fockT τ (sgB pS) (sgB pT) (BT⁻¹ * XT * BT) P =
      quadOp τ sS BS XS sT BT XT pS pT P + halfTrJ sS BS XS sT BT XT pS pT • P := by
  classical
  obtain ⟨uS, nS, cS⟩ := onb_facts hS
  obtain ⟨uT, nT, cT⟩ := onb_facts hT
  set Xf := BS⁻¹ * XS * BS with hXf
  set Yf := BT⁻¹ * XT * BT with hYf
  have lX : ∀ a b, conj (Xf a b) = -(sgn (sgB pS a) * sgn (sgB pS b)) * Xf b a := lie_entry' uS nS hX
  have lY : ∀ a b, conj (Yf a b) = -(sgn (sgB pT a) * sgn (sgB pT b)) * Yf b a := lie_entry' uT nT hY
  have hA := aK_conj lX lY
  have q1 : quadOp τ sS BS XS sT BT XT pS pT P = ∑ k, ∑ l, gT (eV τ) (pp pS pT) (aK Xf Yf) P k l := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mCoef_eq uS uT cS cT, nCoef_eq uS uT cS cT]
    rfl
  have q2 := sum_eq (eV τ) (eV_inj τ) (pp pS pT) (aK Xf Yf) hA P
  have q3 := sum_aK (C : ℂ →+* MvPolynomial (FVar D m n) ℂ) Xf Yf (tT τ pS pT P)
  have q4 : ∑ j, ∑ k, ∑ i, C (Xf.map (starRingEnd ℂ) j k * (sgn (sgB pS j) * sgn (sgB pS k))) * tT τ pS pT P (i, j) (i, k) =
      -∑ j, ∑ k, ∑ i, (C (Xf k j) : MvPolynomial (FVar D m n) ℂ) * tT τ pS pT P (i, j) (i, k) := by
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    have e : Xf.map (starRingEnd ℂ) j k * (sgn (sgB pS j) * sgn (sgB pS k)) = -Xf k j := by
      rw [Matrix.map_apply, lX j k]
      linear_combination (-(Xf k j) * sgn (sgB pS k) * sgn (sgB pS k)) * sgn_sq (sgB pS j) - Xf k j * sgn_sq (sgB pS k)
    rw [e, C_neg, neg_mul]
  have tr1 : (Xf.map (starRingEnd ℂ)).trace = -Xf.trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, lX, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sgn_sq]
    ring
  have tr2 : ∑ k : Fin m × Fin n, aK Xf Yf k k = (n : ℂ) * Yf.trace - (m : ℂ) * Xf.trace := by
    simp only [Fintype.sum_prod_type, aK_apply, ite_true, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Matrix.trace, Matrix.diag, Finset.mul_sum]
  have sc : halfTrJ sS BS XS sT BT XT pS pT = (1 / 2 : ℂ) * ∑ k, aK Xf Yf k k - ∑ k, (if pp pS pT k then 0 else aK Xf Yf k k) := by
    rw [halfTrJ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mCoef_eq uS uT cS cT, mA, ite_eq_left Iff.rfl, fc]
    by_cases h : pp pS pT k
    · simp only [ite_eq_left h]
      ring
    · have e := hA k k
      rw [ite_eq_left Iff.rfl] at e
      rw [ite_eq_right h, ite_eq_right h, e]
      ring
  have hR : ∑ k, (if pp pS pT k then 0 else C (aK Xf Yf k k) * P) =
      (∑ k, (if pp pS pT k then 0 else aK Xf Yf k k)) • P := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · simp
    · rw [C_mul']
  have hq : ∑ i, ∑ l, ∑ j, C (Yf i l) * tT τ pS pT P (i, j) (l, j) =
      quadOp τ sS BS XS sT BT XT pS pT P - (∑ k, (if pp pS pT k then 0 else aK Xf Yf k k)) • P +
        ∑ j, ∑ k, ∑ i, C (Xf k j) * tT τ pS pT P (i, j) (i, k) := by
    refine eq_add_of_sub_eq ?_
    rw [q1, ← hR, ← q2, ← q3]
    rfl
  rw [fockS_apply, fockT_apply, q4, sc, tr1, tr2, hq]
  module

end Final

end Concrete

end GlobalTheory.WeilReal.QuadAlg
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PderivComm =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunctionStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunctionStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunction\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

theorem _root_.GlobalTheory.T.exists_nonzero_fockVacuum_of_nonzero_thetaFunction : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → f ≠ 0 → ∃ f₀, GlobalTheory.ChainFr.IsVacF ψ θ A B f₀ ∧ f₀ ≠ 0 := by
  first | exact @GlobalTheory.Mem.VacReal.exists_isVacF_ne_zero
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunctionStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealLieAlgebraActsByFockOperatorsUpToScalarsStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealLieAlgebraActsByFockOperatorsUpToScalarsStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealLieAlgebraActsByFockOperatorsUpToScalars\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

theorem _root_.GlobalTheory.T.realLieAlgebra_acts_by_fockOperators_upToScalars : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∃ (κS : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) (κT : Matrix (Fin W.rank) (Fin W.rank) ℂ → ℂ), ∀ f, IsThetaFunO ψ V W f → IsFockVacAt (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) f → GlobalTheory.ChainFr.LieFockWith ψ θ A B ω f τ κS κT := by
  first | exact @GlobalTheory.LieFock.lieFockUpTo_at
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealLieAlgebraActsByFockOperatorsUpToScalarsStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAdd =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAdd", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane\npublic import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth\nimport Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain\nimport Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart\nimport Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor\nimport Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcrOperatorsThetaFunctions\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebra\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationOneParameterGenerator\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfNorms\nimport Formalism.LocalToGlobal.IndefiniteForms.IndefSide\nimport Formalism.LocalToGlobal.IndefiniteReal.LinksDefs\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.LieSum

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Mem.LiftGen Filter
open scoped Topology Classical

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem hasDerivAt_apply {u : ℝ → BB ψ S T} {A : BB ψ S T} (hu : HasDerivAt u A 0) {f : ℝ → WO S T → ℂ}
    (e : ∀ t, ((u t).1 : WO S T → ℂ) = f t) (w : WO S T) :
    HasDerivAt (fun t => f t w) ((A.1 : WO S T → ℂ) w) 0 := by
  have h3 := ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (congrFun (e t) w).symm)

theorem theta_nOp {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ)
    (hψ : IsStdChar D ψ (-1)) (X : Matrix (Ix S T) (Ix S T) ℂ) (F : BB ψ S T) (hF : IsThetaFunO ψ S T F.1)
    (l : ℂ) : IsThetaFunO ψ S T (nOp (rhoV hψ σ S T) (HM S T) X F + l • F).1 := by
  let J : thetaSub ψ S T →ₗ[ℂ] BB ψ S T :=
    { toFun := fun f => toB hψ f.1 f.2
      map_add' := fun f g => QB_ext fun x => rfl
      map_smul' := fun a f => QB_ext fun x => rfl }
  have hc : ∀ f, ((J f).1 : WO S T → ℂ) = f.1 := fun f => coe_toB hψ f.1 f.2
  have hJ : Function.Injective J := fun f g e => Subtype.ext (by rw [← hc, ← hc, e])
  have ht : ∀ f, IsThetaFunO ψ S T (J f).1 := fun f => (hc f).symm ▸ f.2
  have hs : ∀ f, Sm (rhoV hψ σ S T) (J f) := fun f => sm_of_theta h hψ _ (ht f)
  have hk : ∀ v f, ∃ g, J g = dH (rhoV hψ σ S T) v (J f) := by
    intro v f
    obtain ⟨F', hF', hd⟩ := exists_deriv h hψ (J f) (ht f) v
    refine ⟨⟨F'.1, hF'⟩, QB_ext fun w => ?_⟩
    rw [hc]
    exact (hd w).unique (((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v (hs f)))
  obtain ⟨x, d, -, hn⟩ := GlobalTheory.Mem.Lift.ThOps.exists_ops (HM S T) HM_herm HM_det (rhoV hψ σ S T) (isHeis_rhoB h hψ) J hJ hs hk
  have hxd : ∀ (X : Matrix (Ix S T) (Ix S T) ℂ) (f : thetaSub ψ S T) (F : BB ψ S T),
      (F.1 : WO S T → ℂ) = f.1 → ((∑ k, ∑ l, X k l • (x k * d l)) f).1 = (nOp (rhoV hψ σ S T) (HM S T) X F).1 := by
    intro X f F hF
    have e : F = J f := QB_ext fun w => by rw [hF, hc]
    rw [e, ← hn, hc]
  have h1 := ((∑ k, ∑ l, X k l • (x k * d l)) ⟨F.1, hF⟩).2
  rw [hxd X ⟨F.1, hF⟩ F rfl] at h1
  exact (thetaSub ψ S T).add_mem h1 ((thetaSub ψ S T).smul_mem l hF)

theorem isLittleO_rem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (Φ : BB ψ S T →L[ℂ] H)
    {u : ℝ → BB ψ S T} {A : BB ψ S T} (hu : HasDerivAt u A 0) :
    (fun t : ℝ => Φ (u t - u 0 - (t : ℂ) • A)) =o[𝓝 0] fun t => t := by
  have h : HasDerivAt (fun t => Φ (u t)) (Φ A) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  rw [hasDerivAt_iff_isLittleO] at h
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_) (Filter.Eventually.of_forall fun t => sub_zero t)
  beta_reduce
  rw [sub_zero, map_sub, map_sub, map_smul, Complex.coe_smul]

theorem hasDerivAt_of_rem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (Φ : BB ψ S T →L[ℂ] H)
    {u : ℝ → BB ψ S T} {A : BB ψ S T} (h : (fun t : ℝ => Φ (u t - u 0 - (t : ℂ) • A)) =o[𝓝 0] fun t => t) :
    HasDerivAt (fun t => Φ (u t)) (Φ A) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_) (Filter.Eventually.of_forall fun t => (sub_zero t).symm)
  beta_reduce
  rw [sub_zero, map_sub, map_sub, map_smul, Complex.coe_smul]



theorem image_deriv_add {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (Φ : BB ψ S T →L[ℂ] H)
    {u₁ u₂ u₃ v : ℝ → BB ψ S T} {A₁ A₂ A₃ B : BB ψ S T}
    (d₁ : HasDerivAt u₁ A₁ 0) (d₂ : HasDerivAt u₂ A₂ 0) (d₃ : HasDerivAt u₃ A₃ 0) (dv : HasDerivAt v B 0)
    (z₁ : u₃ 0 = u₁ 0) (zv : v 0 = A₂)
    (hnorm : ∀ t : ℝ, ‖Φ (u₃ t - u₁ t - (t : ℂ) • v t)‖ = ‖Φ (u₂ t - u₂ 0 - (t : ℂ) • A₂)‖) :
    Φ A₃ = Φ (A₁ + A₂) := by
  have hid : ∀ t : ℝ, u₃ t - u₃ 0 - (t : ℂ) • (A₁ + A₂) = (u₃ t - u₁ t - (t : ℂ) • v t) +
      (t : ℂ) • (v t - v 0) + (u₁ t - u₁ 0 - (t : ℂ) • A₁) := fun t => by
    rw [z₁, zv]
    simp only [smul_sub, smul_add]
    abel
  have hD : HasDerivAt (fun t => Φ (u₃ t)) (Φ (A₁ + A₂)) 0 := by
    apply hasDerivAt_of_rem
    have o1 := isLittleO_rem Φ d₁
    have o2' := (isLittleO_rem Φ d₂).norm_left
    have o2 : (fun t : ℝ => Φ (u₃ t - u₁ t - (t : ℂ) • v t)) =o[𝓝 0] fun t => t := by
      rw [← Asymptotics.isLittleO_norm_left]
      exact o2'.congr_left fun t => (hnorm t).symm
    have hg : Tendsto (fun t => Φ (v t - v 0)) (𝓝 0) (𝓝 0) := by
      have := ((Φ.continuous.tendsto _).comp dv.continuousAt).sub_const (Φ (v 0))
      rw [sub_self] at this
      refine this.congr fun t => ?_
      simp only [Function.comp, map_sub]
    have o3 : (fun t : ℝ => Φ ((t : ℂ) • (v t - v 0))) =o[𝓝 0] fun t => t := by
      have := (Asymptotics.isBigO_refl (fun t : ℝ => t) (𝓝 0)).smul_isLittleO
        ((Asymptotics.isLittleO_one_iff ℝ).2 hg)
      refine this.congr (fun t => ?_) (fun t => ?_)
      · beta_reduce
        rw [map_smul, Complex.coe_smul]
      · simp
    have hΦ : ∀ t : ℝ, Φ (u₃ t - u₃ 0 - (t : ℂ) • (A₁ + A₂)) = Φ (u₃ t - u₁ t - (t : ℂ) • v t) +
        Φ ((t : ℂ) • (v t - v 0)) + Φ (u₁ t - u₁ 0 - (t : ℂ) • A₁) := fun t => by
      rw [hid t, map_add (f := _), map_add (f := _)]
    exact ((o2.add o3).add o1).congr_left fun t => (hΦ t).symm
  have h3 : HasDerivAt (fun t => Φ (u₃ t)) (Φ A₃) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) d₃
  exact h3.unique hD



theorem sum_of_curves (hψ : IsStdChar D ψ (-1)) {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : GlobalTheory.Ker.IsWeak ψ S T om) (γ₁ γ₂ : ℝ → GA D S × GA D T) (h₁ : γ₁ 0 = 1) (h₂ : γ₂ 0 = 1)
    (F : WO S T → ℂ) (hF : IsThetaFunO ψ S T F) {u₁ u₂ u₃ v : ℝ → BB ψ S T} {A₁ A₂ A₃ B : BB ψ S T}
    (e₁ : ∀ t, ((u₁ t).1 : WO S T → ℂ) = om (γ₁ t) F)
    (e₂ : ∀ t, ((u₂ t).1 : WO S T → ℂ) = om (γ₂ t) F)
    (e₃ : ∀ t, ((u₃ t).1 : WO S T → ℂ) = om (γ₁ t * γ₂ t) F)
    (ev : ∀ t, ((v t).1 : WO S T → ℂ) = om (γ₁ t) A₂.1)
    (d₁ : HasDerivAt u₁ A₁ 0) (d₂ : HasDerivAt u₂ A₂ 0) (d₃ : HasDerivAt u₃ A₃ 0) (dv : HasDerivAt v B 0)
    (hA₂ : IsThetaFunO ψ S T A₂.1) : (A₃.1 : WO S T → ℂ) = A₁.1 + A₂.1 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hk : ∀ (p : GA D S × GA D T) (a b : BB ψ S T), IsThetaFunO ψ S T b.1 → (a.1 : WO S T → ℂ) = om p b.1 →
      ‖toL2 _ _ (μ.restrict 𝓕) a‖ = ‖toL2 _ _ (μ.restrict 𝓕) b‖ := by
    intro p a b hb hab
    rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2, hab]
    exact hW.om_unit μ 𝓕 hμ h𝓕 p _ hb
  have z₁ : u₃ 0 = u₁ 0 := QB_ext fun x => congrFun
    (by rw [e₃, e₁, h₁, h₂, one_mul] : ((u₃ 0).1 : WO S T → ℂ) = (u₁ 0).1) x
  have z₂ : ((u₂ 0).1 : WO S T → ℂ) = F := by rw [e₂, h₂, map_one, Module.End.one_apply]
  have zv : v 0 = A₂ := QB_ext fun x => congrFun
    (by rw [ev, h₁, map_one, Module.End.one_apply] : ((v 0).1 : WO S T → ℂ) = A₂.1) x
  have th₂ : ∀ t, IsThetaFunO ψ S T (u₂ t).1 := fun t => by rw [e₂]; exact hW.om_pres _ _ hF
  have hnorm : ∀ t : ℝ, ‖toL2 _ _ (μ.restrict 𝓕) (u₃ t - u₁ t - (t : ℂ) • v t)‖ =
      ‖toL2 _ _ (μ.restrict 𝓕) (u₂ t - u₂ 0 - (t : ℂ) • A₂)‖ := fun t => by
    have ea : ((u₃ t - u₁ t - (t : ℂ) • v t).1 : WO S T → ℂ) =
        ((u₃ t).1 : WO S T → ℂ) - (u₁ t).1 - (t : ℂ) • ((v t).1 : WO S T → ℂ) := rfl
    have eb : ((u₂ t - u₂ 0 - (t : ℂ) • A₂).1 : WO S T → ℂ) =
        ((u₂ t).1 : WO S T → ℂ) - (u₂ 0).1 - (t : ℂ) • (A₂.1 : WO S T → ℂ) := rfl
    refine hk (γ₁ t) _ _ ?_ ?_
    · rw [eb]
      exact (thetaSub ψ S T).sub_mem ((thetaSub ψ S T).sub_mem (th₂ t) (th₂ 0)) ((thetaSub ψ S T).smul_mem _ hA₂)
    · rw [ea, eb, z₂, e₃, e₁, ev, e₂, map_mul, Module.End.mul_apply, map_sub, map_sub, map_smul]
  have key : toL2 _ _ (μ.restrict 𝓕) A₃ = toL2 _ _ (μ.restrict 𝓕) (A₁ + A₂) :=
    image_deriv_add _ d₁ d₂ d₃ dv z₁ zv hnorm
  have h4 := lintegral_norm_sq_eq_toL2 (μ.restrict 𝓕) (A₃ - (A₁ + A₂))
  rw [map_sub, key, sub_self, enorm_zero, zero_pow two_ne_zero,
    lintegral_eq_zero_iff ((A₃ - (A₁ + A₂)).1.continuous.measurable.enorm.pow_const 2)] at h4
  have h5 := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ (A₃ - (A₁ + A₂)).1.continuous
    (BB_norm_periodic hψ _) (by filter_upwards [h4] with x hx; simpa using hx)
  exact sub_eq_zero.1 h5

end GlobalTheory.Mem.LieSum



open Classical in
theorem GlobalTheory.Mem.LieSum.hasDerivAt_add : ∀ (D : D7) (V W : HSp D) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt W τ, ∀ F F₁ F₂ : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) F z) (F₁ z) 0) → (∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) F z) (F₂ z) 0) → ∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, oneP θ W τ Y t) F z) (F₁ z + F₂ z) 0 := by
  intro D V W θ ψ χS χT ω τ hθ hω X hX Y hY F F₁ F₂ hF h₁ h₂ z
  have hψ := hω.std
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hW := GlobalTheory.Ker.isWeak_of_datum hω
  have hc := hω.om_cont
  let γ₁ : ℝ → GA D V × GA D W := fun t => (oneP θ V τ X t, 1)
  let γ₂ : ℝ → GA D V × GA D W := fun t => (1, oneP θ W τ Y t)
  let γ₃ : ℝ → GA D V × GA D W := fun t => (oneP θ V τ X t, oneP θ W τ Y t)
  have hγ : ∀ t, γ₃ t = γ₁ t * γ₂ t := fun t => by
    simp only [γ₁, γ₂, γ₃, Prod.mk_mul_mk, mul_one, one_mul]
  have m₁ : ∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ V W (γ₁ t) k l)
      (GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ (-X)) k l) 0 := fun k l => by
    simp only [γ₁, GlobalTheory.RealWeil.mM_apply, GlobalTheory.Mem.Lift.WeylAction.oneP_inv hθ hX, GlobalTheory.WeilVacMove.mt_one,
      GlobalTheory.WeilVacMove.compAt_one, GlobalTheory.Mem.Lift.WeylAction.blk_apply]
    split_ifs
    · exact (GlobalTheory.Mem.Lift.WeylAction.hasDerivAt_comp hθ (GlobalTheory.Mem.Lift.WeylAction.neg_mem_lieAt hX) _ _ _).const_mul _
    · exact hasDerivAt_const _ _
  have m₂ : ∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ V W (γ₂ t) k l)
      (GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) k l) 0 := fun k l => by
    simp only [γ₂, GlobalTheory.RealWeil.mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one,
      GlobalTheory.Mem.Lift.WeylAction.blk_apply]
    split_ifs
    · exact (GlobalTheory.Mem.Lift.WeylAction.hasDerivAt_comp hθ hY _ _ _).mul_const _
    · exact hasDerivAt_const _ _
  have m₃ : ∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ V W (γ₃ t) k l)
      (∑ j, (GlobalTheory.RealWeil.blk (fun _ => 1) (Pi.single τ (-X)) k j * GlobalTheory.RealWeil.mM θ V W (γ₂ 0) j l +
        GlobalTheory.RealWeil.mM θ V W (γ₁ 0) k j * GlobalTheory.RealWeil.blk (Pi.single τ Y) (fun _ => 1) j l)) 0 :=
    fun k l => by
      simp only [hγ, map_mul, Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun j _ => (m₁ k j).mul (m₂ j l)
  obtain ⟨l₁, g₁⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ h ψ hψ V W ω hW hc γ₁
    ((GlobalTheory.Mem.Lift.continuous_oneP hθ hX).prodMk continuous_const)
    (fun s t => by simp only [γ₁]; rw [GlobalTheory.Mem.Lift.oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
    (fun t => ⟨(GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t).1, one_mem _⟩) _ m₁
  obtain ⟨l₂, g₂⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ h ψ hψ V W ω hW hc γ₂
    (continuous_const.prodMk (GlobalTheory.Mem.Lift.continuous_oneP hθ hY))
    (fun s t => by simp only [γ₂]; rw [GlobalTheory.Mem.Lift.oneP_add hθ hY, Prod.mk_mul_mk, one_mul])
    (fun t => ⟨one_mem _, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t).1⟩) _ m₂
  obtain ⟨l₃, g₃⟩ := GlobalTheory.Mem.Lift.GenZero.exists_generator D θ σ h ψ hψ V W ω hW hc γ₃
    ((GlobalTheory.Mem.Lift.continuous_oneP hθ hX).prodMk (GlobalTheory.Mem.Lift.continuous_oneP hθ hY))
    (fun s t => by simp only [γ₃]; rw [GlobalTheory.Mem.Lift.oneP_add hθ hX, GlobalTheory.Mem.Lift.oneP_add hθ hY, Prod.mk_mul_mk])
    (fun t => ⟨(GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t).1, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t).1⟩) _ m₃
  have eF := GlobalTheory.RealWeil.coe_toB hψ F hF
  have hFb : IsThetaFunO ψ V W (GlobalTheory.RealWeil.toB hψ F hF).1 := by rw [eF]; exact hF
  obtain ⟨u₁, e₁, d₁⟩ := g₁ _ hFb
  obtain ⟨u₂, e₂, d₂⟩ := g₂ _ hFb
  obtain ⟨u₃, e₃, d₃⟩ := g₃ _ hFb
  have hA₂ := GlobalTheory.Mem.LieSum.theta_nOp h hψ (GlobalTheory.RealWeil.blk (Pi.single τ Y) fun _ => 1) _ hFb l₂
  obtain ⟨v, ev, dv⟩ := g₁ _ hA₂
  rw [eF] at e₁ e₂ e₃
  have k₁ := GlobalTheory.Mem.LieSum.hasDerivAt_apply d₁ e₁ z
  have k₂ := GlobalTheory.Mem.LieSum.hasDerivAt_apply d₂ e₂ z
  have k₃ := GlobalTheory.Mem.LieSum.hasDerivAt_apply d₃ e₃ z
  have hs := GlobalTheory.Mem.LieSum.sum_of_curves hψ hW γ₁ γ₂
    (by simp only [γ₁]; rw [GlobalTheory.Mem.Lift.oneP_zero hθ]; rfl)
    (by simp only [γ₂]; rw [GlobalTheory.Mem.Lift.oneP_zero hθ]; rfl) F hF e₁ e₂ (fun t => by rw [e₃, hγ]) ev d₁ d₂ d₃ dv hA₂
  rw [hs, Pi.add_apply, k₁.unique (h₁ z), k₂.unique (h₂ z)] at k₃
  exact k₃
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAdd =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAddStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAddStatement", "h": "module\n\npublic import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth\npublic import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAdd\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Formalism.LocalToGlobal.IndefiniteForms.IndefSide\nimport Formalism.LocalToGlobal.IndefiniteReal.LinksDefs\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

theorem _root_.GlobalTheory.T.weilDatum_realPlaceDerivatives_add : ∀ (D : D7) (V W : HSp D) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt W τ, ∀ F F₁ F₂ : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) F z) (F₁ z) 0) → (∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) F z) (F₂ z) 0) → ∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, oneP θ W τ Y t) F z) (F₁ z + F₂ z) 0 := by
  first | exact @GlobalTheory.Mem.LieSum.hasDerivAt_add
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAddStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealDerivativeFockVectorsAll =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealDerivativeFockVectorsAll", "h": "module\n\npublic import Formalism.LocalToGlobal.IndefiniteReal.WeilFull\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PderivComm\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunctionStatement\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealLieAlgebraActsByFockOperatorsUpToScalarsStatement\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAddStatement\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTraceStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.WeilReal

open GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.WeilReal.QuadAlg Formalism.IndefR.Fock.Sk

def frOf {D : D7} (V : HSp D) (s B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : D.what₂.Tau → ℕ)
    (h : ∀ τ, IsONBasis (gramAt D V τ) (s τ) (B τ) (p τ)) : Fr V where
  ε τ := sgB (p τ)
  fr τ := (B τ)⁻¹
  fr_unit τ := (isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ (onb_facts (h τ)).1)
  fr_gram τ := by
    obtain ⟨u, g, -⟩ := onb_facts (h τ)
    rw [← g]
    have h1 : ((B τ)⁻¹)ᴴ * (B τ)ᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ u, conjTranspose_one]
    calc _ = (((B τ)⁻¹)ᴴ * (B τ)ᴴ) * gramAt D V τ * (B τ * (B τ)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, mul_nonsing_inv _ u, Matrix.one_mul, Matrix.mul_one]

variable {D : D7} {V : HSp D} {s B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {p : D.what₂.Tau → ℕ}

theorem frOf_onb (h : ∀ τ, IsONBasis (gramAt D V τ) (s τ) (B τ) (p τ)) : (frOf V s B p h).onb = B := by
  funext τ
  exact nonsing_inv_nonsing_inv _ (onb_facts (h τ)).1

theorem frOf_cart (h : ∀ τ, IsONBasis (gramAt D V τ) (s τ) (B τ) (p τ)) : (frOf V s B p h).cart = s := by
  funext τ
  obtain ⟨u, -, c⟩ := onb_facts (h τ)
  change ((B τ)⁻¹)⁻¹ * Formalism.REAL.Jm (sgB (p τ)) * (B τ)⁻¹ = s τ
  rw [nonsing_inv_nonsing_inv _ u, ← c, mul_nonsing_inv_cancel_right _ _ u]

theorem pure_zero {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i, A i 0 = 0) (P : MvPolynomial ι ℂ) :
    pureTensorL A (0 : X → ℂ) P = 0 := by
  have h : ∀ l : List ι, l.foldr (fun i g => A i g) (0 : X → ℂ) = 0 := fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.foldr_cons, ih, hA]
  have hz : pureTensorL A (0 : X → ℂ) = 0 := (MvPolynomial.basisMonomials ι ℂ).ext fun k => by
    simp only [pureTensorL, Module.Basis.constr_basis, LinearMap.zero_apply]
    exact h _
  rw [hz, LinearMap.zero_apply]

end GlobalTheory.WeilReal

namespace GlobalTheory.WeilReal

open GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.WeilReal.QuadAlg Formalism.IndefR.Fock.Sk

theorem comb {R : Type} [AddCommGroup R] [Module ℂ R] (a b q P : R) (h c d : ℂ) (hq : a + b = q + h • P) :
    q + (h + c - d) • P = (a + (-d) • P) + (b + c • P) := by
  have e : q = a + b - h • P := eq_sub_of_add_eq hq.symm
  rw [e]
  module

theorem realAllO : ∀ D : D7, Formalism.IndefR.WeilFull.RealAllO D := by
  intro D ψ S T χS χT om hd _ θ sS sT BS BT pS pT hp τ αS αT hαS hαT XS XT hXS hXT f hf hv P x
  obtain ⟨A, hA⟩ : ∃ A : Fr S, A = frOf S sS BS pS hp.onbS := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fr T, B = frOf T sT BT pT hp.onbT := ⟨_, rfl⟩
  have cA : A.cart = sS := hA ▸ frOf_cart hp.onbS
  have cB : B.cart = sT := hB ▸ frOf_cart hp.onbT
  have oA : A.onb = BS := hA ▸ frOf_onb hp.onbS
  have oB : B.onb = BT := hB ▸ frOf_onb hp.onbT
  have eA : A.ε τ = sgB (pS τ) := by rw [hA]; rfl
  have eB : B.ε τ = sgB (pT τ) := by rw [hB]; rfl
  have rA : A.fr τ = (BS τ)⁻¹ := by rw [hA]; rfl
  have rB : B.fr τ = (BT τ)⁻¹ := by rw [hB]; rfl
  have pt : pureTensorO ψ θ S T sS sT BS BT f = ptF ψ θ A B f := by
    rw [ptF, cA, cB, oA, oB]
  rw [pt]
  have lin : ∀ (g : WO S T → ℂ) (Q Q' : MvPolynomial (FVar D T.rank S.rank) ℂ),
      ptF ψ θ A B g (Q + Q') = ptF ψ θ A B g Q + ptF ψ θ A B g Q' := fun g Q Q' =>
    map_add (pureTensorO ψ θ S T A.cart B.cart A.onb B.onb g) Q Q'
  have lsm : ∀ (g : WO S T → ℂ) (c : ℂ) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ),
      ptF ψ θ A B g (c • Q) = c • ptF ψ θ A B g Q := fun g c Q =>
    map_smul (pureTensorO ψ θ S T A.cart B.cart A.onb B.onb g) c Q
  by_cases f0 : f = 0
  · subst f0
    have z0 : ∀ Q, ptF ψ θ A B 0 Q = 0 := fun Q => by
      refine pure_zero _ (fun k => ?_) Q
      funext y
      simp [aPlusAll, aPlus, crea, Datum.dRho, heisO]
    simp only [z0, map_zero]
    exact hasDerivAt_const _ _
  obtain ⟨f₀, hv0, hne⟩ := GlobalTheory.T.exists_nonzero_fockVacuum_of_nonzero_thetaFunction D S T A B θ ψ hp.std hp.inf f hf f0
  obtain ⟨κS, κT, hκ⟩ := GlobalTheory.T.realLieAlgebra_acts_by_fockOperators_upToScalars D S T A B θ ψ χS χT om τ hp.inf hd
  have k0 := hκ f₀ hv0.1 (hv0.2 τ)
  have all := GlobalTheory.T.lieAction_fockOperators_scalars_trace D S T A B θ ψ χS χT om f₀ τ αS αT hp.inf hd hαS hαT hv0
  obtain ⟨z, hz⟩ := Function.ne_iff.1 hne
  have hz' : f₀ z ≠ 0 := hz
  have one : ∀ c : ℂ, ptF ψ θ A B f₀ (c • (1 : MvPolynomial _ ℂ)) z = c * f₀ z := fun c => by
    rw [lsm]
    have e1 : ptF ψ θ A B f₀ 1 = f₀ := GlobalTheory.FockIndep.pure_one f₀
    rw [e1]
    rfl
  have eS : κS XS = -((αT : ℂ) * XS.trace) := by
    have e := (k0.1 XS hXS 1 z).unique (all.1 XS hXS 1 z)
    rw [lin, lin, Pi.add_apply, Pi.add_apply, add_right_inj, one, one] at e
    exact mul_right_cancel₀ hz' e
  have eT : κT XT = (αS : ℂ) * XT.trace := by
    have e := (k0.2 XT hXT 1 z).unique (all.2 XT hXT 1 z)
    rw [lin, lin, Pi.add_apply, Pi.add_apply, add_right_inj, one, one] at e
    exact mul_right_cancel₀ hz' e
  have kf := hκ f hf (by rw [cA, cB]; exact hv)
  have ht : IsThetaFunO ψ S T (ptF ψ θ A B f P) :=
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hp.std hp.inf _ _ _ _ hf P
  have sm := GlobalTheory.T.weilDatum_realPlaceDerivatives_add D S T θ ψ χS χT om τ hp.inf hd XS hXS XT hXT _ _ _ ht (kf.1 XS hXS P) (kf.2 XT hXT P) x
  have uS := (onb_facts (hp.onbS τ)).1
  have uT := (onb_facts (hp.onbT τ)).1
  have frA : (A.fr τ * XS * (A.fr τ)⁻¹) = (BS τ)⁻¹ * XS * BS τ := by
    rw [rA, nonsing_inv_nonsing_inv _ uS]
  have frB : (B.fr τ * XT * (B.fr τ)⁻¹) = (BT τ)⁻¹ * XT * BT τ := by
    rw [rB, nonsing_inv_nonsing_inv _ uT]
  have q := fock_eq_quad τ (pS τ) (pT τ) (hp.onbS τ) (hp.onbT τ) hXS hXT P
  have e : ptF ψ θ A B f (quadOp τ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) P +
      (halfTrJ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) + (αS : ℂ) * XT.trace - (αT : ℂ) * XS.trace) • P) x =
      ptF ψ θ A B f (fockS τ (A.ε τ) (B.ε τ) ((A.fr τ * XS * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P + κS XS • P) x +
      ptF ψ θ A B f (fockT τ (A.ε τ) (B.ε τ) (B.fr τ * XT * (B.fr τ)⁻¹) P + κT XT • P) x := by
    rw [← Pi.add_apply (ptF ψ θ A B f _), ← lin, frA, frB, eS, eT, eA, eB, comb _ _ _ _ _ _ _ q]
  rw [e]
  exact sm

end GlobalTheory.WeilReal

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealDerivativeFockVectorsAll =====
