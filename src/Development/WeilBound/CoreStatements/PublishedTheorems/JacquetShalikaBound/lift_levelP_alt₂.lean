module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.CMMul
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.LFun GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace PositivityTheory.JacquetShalikaLocal

def lift_levelP_alt₂ : Prop := ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)),
  qF (w.adicCompletion E) = Ideal.absNorm w.asIdeal ∧ ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (v : V) (z : Fin n → ℂˣ),
    IsSatVecGL w ρ v (Finset.univ.val.map z) → Heig ρ v z

def G1 : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a),
  (CG.mk π).IsUnitary → ∀ w : HeightOneSpectrum (𝓞 E), ∃ B, Unit' (π.locRep w) B

def G2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
  (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), HasSatGL w (π.locRep w) B → ∀ l : π.V →ₗ[ℂ] ℂ, l ≠ 0 →
    ∃ v g, IsSatVecGL w (π.locRep w) v B ∧ l (π.locRep w g v) ≠ 0

def G3 : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
  (w : HeightOneSpectrum (𝓞 E)), Smooth (π.locRep w)

def G4 : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a)
  (w : HeightOneSpectrum (𝓞 E)), ∃ ψ, PsiOK ψ ∧ ∃ l : π.V →ₗ[ℂ] ℂ, l ≠ 0 ∧ Whit (π.locRep w) ψ l

end PositivityTheory.JacquetShalikaLocal

end
