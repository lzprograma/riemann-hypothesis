module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

namespace UpperTheory.V.Z.Sym.Ga

variable {k : Type} [Field k]

abbrev tr {n : ℕ} (g : GL (Fin n) k) : k := (g : Matrix (Fin n) (Fin n) k).trace

def uf (g : GL (Fin 2) k) : k := tr g ^ 2 / (g : Matrix (Fin 2) (Fin 2) k).det - 2

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] {l : ℕ} [Fact l.Prime]

abbrev ep (l : ℕ) [Fact l.Prime] (g : G L Ω) : Qbar l := (cycBar L Ω l g : Qbar l)

def Bad (r : G L Ω →* GL (Fin 2) (Qbar l)) : Set (G L Ω) :=
  {g | ∃ m : ℤ, |m| ≤ 2 ∧ uf (r g) ^ 2 - 2 = ep l g ^ m + ep l g ^ (-m)}

def FrobAt (w : Plc L) (s : G L Ω) : Prop := ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ IsFrob A (normV w) s

variable [IsCMField L] [IsAlgClosure L Ω]

structure GoodSet (ι : Qbar l ≃+* ℂ) (M : ℕ) (r : G L Ω →* GL (Fin 2) (Qbar l)) (σ : Submodule ℂ (UA L 2 → ℂ)) (P : Set (Plc L))
    (ψ : ∀ w : Plc L, Fin 2 → (Kw w)ˣ →* ℂˣ) : Prop where
  mem : ∀ w ∈ P, IsSplitAt w ∧ ((l : ℕ) : 𝓞 L) ∉ w.asIdeal ∧ CompEq σ w (ψ w)
  meets : ∀ w, IsSplitAt w → (M : 𝓞 L) ∉ w.asIdeal → (∃ s, FrobAt w s ∧ s ∉ Bad r) →
    ∃ w' ∈ P, w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))

end UpperTheory.V.Z.Sym.Ga

end
