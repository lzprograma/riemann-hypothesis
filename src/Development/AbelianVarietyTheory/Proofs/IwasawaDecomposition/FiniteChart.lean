module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def Chart (u : B.Word) (a : I.ι) (i : ℕ) : Type :=
  Set.range fun c : (I.stp u a i).Cl => (c.1, cosetIn ((I.stp u a i).rep c))

def chartOf (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) : Chart I u a i :=
  ⟨(c.1, cosetIn ((I.stp u a i).rep c)), c, rfl⟩

structure AdmK (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type} (k : Ch → GA B (B.R.N i)) : Prop where
  std : ∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (k β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)
  off : ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v →
    (a = I.mu0 ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (k β) = 1
  T : ∀ β (P : (B.primes X).vT u) (r j : Fin (B.R.N i)), r.1 + 1 = B.R.N i →
    HasRes P.1 (adAt B.host.F P.1 (((k β)⁻¹ : GA B (B.R.N i)).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)

theorem finite_chart (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) : Finite (Chart I u a i) := by
  have h := (l.ch u a).step i
  haveI : Finite (I.stp u a i).Cl := @Finite.instSigma _ _ inferInstance h.fin_orb
  exact (Set.finite_range _).to_subtype

end GlobalTheory.Mem.Col2.TC.ChTw
