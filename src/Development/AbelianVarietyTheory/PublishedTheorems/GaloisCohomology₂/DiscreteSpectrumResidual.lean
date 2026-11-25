module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
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

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.Published

def DiscreteSpectrumResidual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ), 1 ≤ N →
    (∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
      ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d) ∧
    (∀ (a d : ℕ) (π : CuspSub E a), d * a = N → IsNormalised π →
      ∃! V : Submodule ℂ (Sm E N), IsDiscrete V ∧ IsSpehOf V π d) ∧
    (∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d a' d' : ℕ) (π : CuspSub E a) (π' : CuspSub E a'),
      IsNormalised π → IsNormalised π' → IsSpehOf V π d → IsSpehOf V π' d' →
        d = d' ∧ (⟨a, CG.mk π⟩ : Σ b, CG E b) = ⟨a', CG.mk π'⟩) ∧
    (∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → IsIsoGL V V' → V = V') ∧
    ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      IsNormalised π → IsSpehOf V π d → ∀ w, (∃ σ σ', π.IsLocComp w σ ∧ IsLocCompGL V w σ') ∧
        ∀ σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
          GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ

end GlobalTheory.Published

end
