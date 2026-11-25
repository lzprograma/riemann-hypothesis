module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitHeckeElementLabelZerosThenNegOnes
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Formalism.IndefR.Mult Formalism.L2.Theta

namespace GlobalTheory.FrameProdLoc

theorem mem_locGrp_of_isLocEnv {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0)
    (i : ok × ℕ) (x : Bridge.Gf V) (h : isLocEnv V pl ok i x) :
    x ∈ GlobalTheory.HeckeRowsCompare.locGrp V ((pl i.1).under (𝓞 D.host.F)) := by
  rw [GlobalTheory.HeckeRowsCompare.mem_locGrp]
  exact GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 h)

theorem isLocEnv_of_mem {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0)
    (i : ok × ℕ) (x : Bridge.Gf V) (e : Formalism.L2.Theta.AE D) (he : Formalism.L2.NTheta.IsIdemAt e (pl i.1))
    (h : x ∈ GlobalTheory.HeckeRowsCompare.locGrp V ((pl i.1).under (𝓞 D.host.F))) : isLocEnv V pl ok i x := by
  obtain ⟨α, hα, hfin⟩ := GlobalTheory.HeckeRowsCompare.fin_lift V x
  have hI : IsPrimeIdem (pl i.1) e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, hf⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hI
  refine ⟨e, α, he, hα, ?_, ?_⟩
  · show SuppF V (e + cA D e) α
    rw [hf, GlobalTheory.HeckeRowsCompare.suppF_iff V hε hα, hfin]
    exact h
  · rw [← hfin]
    rfl

theorem isLocEnv_prod : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0)
    (i i' : ok × ℕ) (a b c d : Bridge.Gf V), (pl i.1).under (𝓞 D.host.F) = (pl i'.1).under (𝓞 D.host.F) →
    isLocEnv V pl ok i a → isLocEnv V pl ok i' b → isLocEnv V pl ok i' c → isLocEnv V pl ok i d →
    isLocEnv V pl ok i ((c * d)⁻¹ * (a * b)) := by
  intro D V Pl0 pl ok i i' a b c d hv ha hb hc hd
  obtain ⟨e, -, he, -⟩ := id ha
  apply isLocEnv_of_mem V pl ok i _ e he
  have ha' := mem_locGrp_of_isLocEnv V pl ok i a ha
  have hd' := mem_locGrp_of_isLocEnv V pl ok i d hd
  have hb' := mem_locGrp_of_isLocEnv V pl ok i' b hb
  have hc' := mem_locGrp_of_isLocEnv V pl ok i' c hc
  rw [← hv] at hb' hc'
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hc' hd')) (Subgroup.mul_mem _ ha' hb')

end GlobalTheory.FrameProdLoc
