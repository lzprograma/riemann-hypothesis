module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WittIdxOfParallelSig
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
import Mathlib.Tactic.Linter.HaveILetI
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

namespace GlobalTheory.ChainOnto.WittTwo

theorem wittIndex_lt_and_two_split : ∀ (D : D7) (c : Com D) (j : ℕ) (s : PiLocalization₂ D), j ≤ D.R.m → s.Is c j → GlobalTheory.Cusp.wittIndex s.V < D.R.t ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro D c j s hj hs
  refine ⟨?_, fun v h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hpar : ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (s.V.gram.map τ) (sigYD D.R j).1 (sigYD D.R j).2 := by
    intro τ
    have h := hs.sigOK τ
    rw [hs.sig τ] at h
    exact h
  obtain ⟨W, hW, e⟩ := (GlobalTheory.Cusp.isGreatest_wittIndex (s.V : HSpace D.host.E)).1
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have h1 := GlobalTheory.ParallelWitt.finrank_le (E := D.host.E) s.V τ (hpar τ) W (fun x hx y hy => by
    have := hW hy
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this x hx)
  have h3 := D.R.three_m_lt_t
  simp only [sigYD] at h1
  omega

end GlobalTheory.ChainOnto.WittTwo
