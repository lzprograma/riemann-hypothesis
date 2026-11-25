module

public import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.EquivariantFiniteGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCMFamHost
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryAdelicQuotientVolumeIsVolume
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj MeasureTheory

namespace GlobalTheory.FinalJoin2

theorem volPairEx_and_finVol : ∀ (D : D7) (V : HSp D), V.SigOK → VolPairEx V ∧ Formalism.L2.Pj.FinVol V := by
  intro D V hs
  have h := GlobalTheory.Mem.Vol.volIs_trueVol _ _ D.sp.cm _ (tauE D) D.cd V
    (GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau) hs
  obtain ⟨⟨μ, hμ⟩, hall⟩ := h
  have hex : VolPairEx V := by
    obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := hall μ hμ
    exact ⟨(μ, 𝓕), hμ, h𝓕⟩
  refine ⟨hex, ?_⟩
  have hp := volPair_isVolPair V hex
  have hm : (volPair V).1 (volPair V).2 =
      ENNReal.ofReal (GlobalTheory.Mem.Vol.trueVol D.sp.cm (tauE D) D.cd V) :=
    (hall _ hp.1).2 _ hp.2
  unfold Formalism.L2.Pj.FinVol
  rw [muQ_univ, hm]
  exact ⟨(ENNReal.ofReal_pos.2 (GlobalTheory.Mem.Vol.trueVol_pos _ _ _ _)).ne', ENNReal.ofReal_ne_top⟩

end GlobalTheory.FinalJoin2
