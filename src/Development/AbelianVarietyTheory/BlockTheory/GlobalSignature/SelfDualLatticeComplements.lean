module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeComplements

open NumberField Formalism.BasicNotions

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def perp (W : HSpace E) (x : W.V) : Submodule E W.V := LinearMap.ker (W.hT x)

def IsSelfDualLattice (W : HSpace E) (L : Submodule (𝓞 E) W.V) : Prop :=
  Submodule.IsLattice E L ∧ Formalism.HermitianLatticesTheory.dual W.hT L = L

def OfKind (W : HSpace E) (M P Q : ℕ) : Prop :=
  W.SigOK ∧ W.rank = M ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def Step (β : E) (P Q P' Q' : ℕ) : Prop :=
  (β = 1 ∧ 1 ≤ P ∧ P' = P - 1 ∧ Q' = Q) ∨ (β = -1 ∧ 1 ≤ Q ∧ P' = P ∧ Q' = Q - 1)

def HasComplement (W : HSpace E) (x : W.V) (M' P' Q' : ℕ) : Prop :=
  ∃ (L : Submodule (𝓞 E) W.V) (W' : HSpace E) (ι : W'.V →ₗ[E] W.V),
    IsSelfDualLattice W L ∧ x ∈ L ∧
    OfKind W' M' P' Q' ∧
    HSpace.IsIsomEmb W' W ι ∧
    LinearMap.range ι = perp W x ∧
    W'.L0.map (ι.restrictScalars (𝓞 E)) = L ⊓ (perp W x).restrictScalars (𝓞 E) ∧
    L = Submodule.span (𝓞 E) {x} ⊔ (L ⊓ (perp W x).restrictScalars (𝓞 E))

def ExistsPerpOver (E : Type) [Field E] [NumberField E] [StarRing E] : Prop :=
  ∀ (W : HSpace E) (M P Q : ℕ), OfKind W M P Q → 3 ≤ M →
    ∀ (β : E) (P' Q' : ℕ), Step β P Q P' Q' →
      ∃ x : W.V, W.hD x x = β ∧ HasComplement W x (M - 1) P' Q'

theorem injective_of_isIsomEmb {W' W : HSpace E} {ι : W'.V →ₗ[E] W.V}
    (h : HSpace.IsIsomEmb W' W ι) : Function.Injective ι := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  refine W'.nondeg.1 y fun z => ?_
  rw [← h y z, hy]
  simp

end General

def UnitVectorPerp (D : D7) : Prop :=
  @ExistsPerpOver D.host.E _ _ D.host.cmStar

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeComplements

end
