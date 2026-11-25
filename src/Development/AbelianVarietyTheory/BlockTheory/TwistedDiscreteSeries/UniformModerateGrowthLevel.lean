module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Matrix
open Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links
open scoped TensorProduct ContDiff

namespace GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions

variable {D : D7} {W : HSp D} {S : D.what₂.Tau → SPar}

def pMinus (M : DSModel W S) (τ : D.what₂.Tau) : Set (Matrix (Fin W.rank) (Fin W.rank) ℂ) :=
  {Z | ∀ a b, ¬ (M.ε τ a = false ∧ M.ε τ b = true) → (M.fr τ * Z * (M.fr τ)⁻¹) a b = 0}

abbrev KMap (M : DSModel W S) : Type :=
  MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => lowT M τ) (GA D W → ℂ)


variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))


variable (W) in
def IsSmoothFn (φ : GA D W → ℂ) : Prop :=
  ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin W.rank) (Fin W.rank) ℂ),
    (∀ i, Xs i ∈ lieAt W (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ W (τs i) (Xs i) (t i)).prod)


variable (W) in
def IsUnifModGrowth (φ : GA D W → ℂ) : Prop :=
  ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin W.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt W p.1) →
    ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC W,
      ‖(l.foldr (fun p f => Rder θ W p.1 p.2 f) φ) (x * g)‖ ≤ C * normInf θ W g ^ N


def RestrictsTo (M : DSModel W S) (T : Formalism.IndefR.Mult.MMap M) (U : KMap M) : Prop :=
  ∀ e : ∀ τ, lowT M τ, T (fun τ => (e τ : M.sm τ)) = U e

theorem single_mem_pMinus (M : DSModel W S) (τ : D.what₂.Tau) {a b : Fin W.rank} (ha : M.ε τ a = false)
    (hb : M.ε τ b = true) : (M.fr τ)⁻¹ * Matrix.single a b (1 : ℂ) * M.fr τ ∈ pMinus M τ := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h : M.fr τ * ((M.fr τ)⁻¹ * Matrix.single a b (1 : ℂ) * M.fr τ) * (M.fr τ)⁻¹ = Matrix.single a b 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  intro c d hcd
  rw [h, Matrix.single_apply, ite_eq_right]
  rintro ⟨rfl, rfl⟩
  exact hcd ⟨ha, hb⟩

end GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions

end
