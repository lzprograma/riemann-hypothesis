module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

namespace GlobalTheory.StepFacNe

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.StepFacNe.chrW_continuous {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    (χ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (h : Continuous χ) {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}
    (τ : E →ₐ[F] _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    Continuous (fun x : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ => (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW χ τ x : ℂ)) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW
  have h1 := _root_.GlobalTheory.LFun.continuous_locChar h (_root_.GlobalTheory.AdelicU.splitPrime τ)
  have h2 := Continuous.units_map
    (_root_.GlobalTheory.LFun.complMap (_root_.GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom
    (_root_.GlobalTheory.LFun.SplitChart.continuous_complMap (_root_.GlobalTheory.AdelicU.splitPrime_under τ))
  exact h1.comp h2


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.StepFacNe.chrW_ram {F E : Type} [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (χ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (h : ¬ _root_.GlobalTheory.LFun.UnrAt χ (_root_.GlobalTheory.AdelicU.splitPrime τ)) :
    ∃ x : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ, (x : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∈ v.adicCompletionIntegers F ∧
      ((x⁻¹ : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)ˣ) : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∈ v.adicCompletionIntegers F ∧
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW χ τ x ≠ 1 := by
  have hw := _root_.GlobalTheory.AdelicU.splitPrime_under τ
  unfold _root_.GlobalTheory.LFun.UnrAt at h
  push Not at h
  obtain ⟨y, hy1, hy2⟩ := h
  unfold _root_.Formalism.L2.Host.IsUnitAt at hy1
  obtain ⟨a, ha⟩ := (_root_.GlobalTheory.LFun.SplitTie.complMap_bijective τ hw).2 (y : _)
  have hv : Valued.v a = 1 := by
    rw [← _root_.GlobalTheory.LFun.SplitTie.valued_complMap τ hw, ha]
    exact hy1
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hv
  refine ⟨Units.mk0 a ha0, ?_, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp [hv]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp [hv]
  · intro h1
    apply hy2
    have hy : Units.map (_root_.GlobalTheory.LFun.complMap hw).toMonoidHom (Units.mk0 a ha0) = y :=
      Units.ext (by simpa using ha)
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.chrW at h1
    rw [MonoidHom.comp_apply, hy] at h1
    exact h1

end GlobalTheory.StepFacNe
