module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
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

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

namespace UpperTheory.V.Z.Sym.Al

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]


variable (n) in
def away (w : Plc L) : Subgroup (UA L n) :=
  ⨅ (u : Plc L) (_ : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))), (cLoc u).ker

def InSpan (w : Plc L) (φ φ' : UA L n → V) : Prop :=
  φ' ∈ Submodule.span ℂ {ψ | ∃ x ∈ locU n w, ψ = fun g => φ (g * x)}

def repOn {π : Submodule ℂ (UA L n → ℂ)} (hπ : IsAutRepU π) : Representation ℂ (UA L n) π where
  toFun x := (RU L n x).restrict fun φ h => hπ.stable x φ h
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

def AF (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (U : Subgroup (UA L n)) : Submodule ℂ (UA L n → V) where
  carrier := {φ | IsAF R U φ}
  add_mem' ha hb := ⟨fun γ h g => by simp [ha.left γ h, hb.left γ h], fun x h g => by simp [ha.inf x h, hb.inf x h],
    fun u h g => by simp [ha.level u h, hb.level u h]⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => by simp, fun _ _ _ => rfl⟩
  smul_mem' c a ha := ⟨fun γ h g => by simp [ha.left γ h], fun x h g => by simp [ha.inf x h], fun u h g => by simp [ha.level u h]⟩

abbrev op (w : Plc L) (W : Sig.Lev (Kw w)) (d : Fin n → (Kw w)ˣ) : Module.End ℂ (UA L n → V) :=
  Hi.dc ((rightReg ℂ (UA L n) V).comp (secW n w)) (W.J n) (W.J n) (Sig.dg d)

def ContCoef {H : Type} [Group H] [TopologicalSpace H] (R : Representation ℂ H V) : Prop :=
  ∀ (x : V) (f : V →ₗ[ℂ] ℂ), Continuous fun g => f (R g x)

end UpperTheory.V.Z.Sym.Al

end
