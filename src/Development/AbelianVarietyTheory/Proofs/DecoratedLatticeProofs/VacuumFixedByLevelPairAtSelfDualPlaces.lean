module

import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodGroupsReduceSplitPlaceFamilySucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeStabilizersFixWeilVacuumOnPlaceSe
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.VacFixP

theorem idAt_eq_bot {D : D7} {P : Pl D → Prop} (hP : ∀ v, ¬ P v) : idAt D P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  refine GlobalTheory.FinPlLoc.eq_zero_of_comp x hx.1 fun w => ?_
  exact (Submodule.mem_iInf _).1 hx.2 ⟨w, hP w⟩

theorem eq_one_of_grpAt {D : D7} {S : HSp D} {P : Pl D → Prop} (hP : ∀ v, ¬ P v) {κ : GA D S}
    (h : κ ∈ grpAt S P) : κ = 1 := by
  first | exact _root_.GlobalTheory.QRed.grpAt_eq_one | exact @_root_.GlobalTheory.QRed.grpAt_eq_one | apply _root_.GlobalTheory.QRed.grpAt_eq_one <;> assumption

theorem vac_fix_on : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T) (P : Pl D → Prop), (∀ v, P v → IsSelfDualC S LS ∧ IsSelfDualC T LT ∧ Tame D v ∧ CharUnramAt D χS v ∧ CharUnramAt D χT v) → ∀ f, Vac ψ S T LS LT P f → ∀ κ κ', InK S LS P κ → InK T LT P κ' → om (κ, κ') f = f := by
  intro D ψ S T χS χT om hW LS LT P hP f hf κ κ' hκ hκ'
  by_cases hex : ∃ v, P v
  · obtain ⟨v, hv⟩ := hex
    obtain ⟨hS, hT, -⟩ := hP v hv
    exact _root_.GlobalTheory.StabSetFix.stab_fix_vac D ψ S T χS χT om hW LS LT hS hT P (fun w hw => (hP w hw).2.2) f hf κ κ' hκ hκ'
  · push Not at hex
    rw [eq_one_of_grpAt hex hκ.1, eq_one_of_grpAt hex hκ'.1, Prod.mk_one_one, map_one]
    rfl

end GlobalTheory.VacFixP
