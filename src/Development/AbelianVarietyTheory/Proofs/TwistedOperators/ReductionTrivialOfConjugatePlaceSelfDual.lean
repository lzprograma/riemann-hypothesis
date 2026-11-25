module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDualFamilySelfDualHermitianSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameIntegralGramMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIntegralAdelicElementExists
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CrdLatEqLatFrame
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical

namespace GlobalTheory.ConjPlaceRedGen



theorem redFn_eq_one_of_conj : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank), IsSelfDualC V L → ∀ β : GL (Fin V.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, Lev.finE V k ∈ Formalism.L2.DIV.St β → ∀ (PP PP' : Formalism.L2.DIV.Pl D.host.E), Formalism.IndefR.Lev.IsConjPl PP' PP → Formalism.L2.DIV.redFn β PP' (Lev.finE V k) = 1 → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  intro D V L hsd β hβ k hk PP PP' hc h1
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D V L hsd
  obtain ⟨G, hG⟩ := GlobalTheory.FrameGram.exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (fun _ => GlobalTheory.LevSplit.sigR_int) (fun _ => rfl) V.gram β _ hβ (fun y hy => (hsd.2 y).1 hy) s s' hs hd
  obtain ⟨h, hh⟩ := hk
  have hU : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ ∈
      Formalism.UG.UJ (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        (V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) := by
    have e : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ = Lev.finE V k := hh
    rw [e]
    exact GlobalTheory.LevSplit.finE_mem_UA V k
  have key := GlobalTheory.FrameMove.conj_gram_sub (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (Formalism.L2.Herm.intAf D.host.F D.host.E) _ β G h hG hU
  rw [← hh, Formalism.L2.DIV.redFn_frGL] at h1 ⊢
  have h1' : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP') h⁻¹ = 1 := by rw [map_inv, h1, inv_one]
  have h2 : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) (G * h * G⁻¹) = 1 := by
    apply Units.ext
    ext i j
    have hz : Formalism.L2.DIV.resS D.host.F PP' ((h⁻¹).val j i) = if j = i then 1 else 0 := by
      have e : ((Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP') h⁻¹ : GL (Fin V.rank) (Formalism.L2.DIV.kP PP')) : Matrix _ _ (Formalism.L2.DIV.kP PP')) j i =
          Formalism.L2.DIV.resS D.host.F PP' ((h⁻¹).val j i) := rfl
      rw [← e, h1', Units.val_one, Matrix.one_apply]
    have h0 := GlobalTheory.ConjPlaceRed.resS_conj_ite D.sp.cm.sig PP' PP hc _ _ (key i j) (j = i) hz
    refine h0.trans ?_
    rw [Units.val_one, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  rw [map_mul, map_mul, map_inv] at h2
  exact _root_.conj_eq_one_iff.1 h2

end GlobalTheory.ConjPlaceRedGen
