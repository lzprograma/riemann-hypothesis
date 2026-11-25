module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.ChrWUnif

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ValuativeRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance locField (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

theorem valued_unifAt (v : Pl F) : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) = WithZero.exp (-1 : ℤ) := by
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  have hu : valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) = uniformizer (Fv F v) :=
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hπv : Valued.v ((π : F) : Fv F v) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hlt : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) < 1 :=
    e.lt_one_iff_lt_one.1 (hu ▸ uniformizer_lt_one)
  have h0 : Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) ≠ 0 := by simp
  have hle1 : valuation (Fv F v) ((π : F) : Fv F v) ≤ valuation (Fv F v) ((unifAt v : (Fv F v)ˣ) : Fv F v) := by
    rw [hu, le_uniformizer_iff]
    exact e.lt_one_iff_lt_one.2 (by rw [hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hge : WithZero.exp (-1 : ℤ) ≤ Valued.v ((unifAt v : (Fv F v)ˣ) : Fv F v) := hπv ▸ (e _ _).1 hle1
  rw [← WithZero.exp_log h0] at hlt hge ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  rw [WithZero.exp_le_exp] at hge
  congr 1
  omega

theorem chrW_unifAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E)
    (v : Pl F) (t : E →ₐ[F] Fv F v) (h : UnrAt χ (splitPrime t)) : chrW χ t (unifAt v) = val χ (splitPrime t) := by
  refine h.locChar_eq_val ?_
  show Valued.v (complMap (splitPrime_under t) ((unifAt v : (Fv F v)ˣ) : Fv F v)) = WithZero.exp (-1 : ℤ)
  rw [GlobalTheory.LFun.SplitTie.valued_complMap t (splitPrime_under t), valued_unifAt]

end GlobalTheory.ChrWUnif
