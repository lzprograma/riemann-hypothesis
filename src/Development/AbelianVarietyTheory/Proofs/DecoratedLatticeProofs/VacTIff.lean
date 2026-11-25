module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.VacAll

def MoveT {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (θ : InfFam (I.rec7 l Z)) (i : ℕ)
    (hi : i + 1 ≤ B.R.m) (c₀ : ℂ) (μ : (AE (I.rec7 l Z))ˣ →* Circle) (om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)))
    (vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ)
    (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) (h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (i + 1))) : Prop :=
  ∀ N N', Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g N → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) h N' →
    ∀ x y, IsDetRoot _ g x → IsDetRoot _ h y →
      ColDat.xiS θ i hi (om (g, h) vac) = fun z => c₀ * (μ x : ℂ)⁻¹ * (μ y : ℂ) * I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N' z

theorem vacT_iff {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {θ : InfFam (I.rec7 l Z)} {i : ℕ}
    {hi : i + 1 ≤ B.R.m} {c₀ : ℂ} {μ : (AE (I.rec7 l Z))ˣ →* Circle} {om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))}
    {vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ} :
    VacT I l Z θ i hi c₀ μ om vac ↔ ∀ g ∈ GfC _, ∀ h ∈ GfC _, MoveT I l Z θ i hi c₀ μ om vac g h := Iff.rfl

theorem xiS_smul {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (θ : InfFam (I.rec7 l Z)) (i : ℕ)
    (hi : i + 1 ≤ B.R.m) (c : ℂ) (F : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) :
    ColDat.xiS θ i hi (c • F) = fun z => c * ColDat.xiS θ i hi F z := by
  funext z
  simp only [ColDat.xiS, xiN, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.AdForm.VacAll
