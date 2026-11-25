module

import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host nonZeroDivisors

namespace GlobalTheory.HeckeProduct

section Comp
variable (L : Type) [Field L] [NumberField L]

theorem localIdele_snd_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion L) : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) v = x
  convert Pi.mulSingle_eq_same v (x : v.adicCompletion L)

theorem localIdele_snd_ne (v w : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion L) : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L) w = 1
  convert Pi.mulSingle_eq_of_ne h (x : v.adicCompletion L)

theorem localIdele_fst (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := rfl

alias infIdele_fst_self := _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self

alias infIdele_fst_ne := _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_ne

end Comp

section Parts
variable (F : Type) [Field F] [NumberField F]

def infPart : Ideles F →* (InfiniteAdeleRing F)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

def finPart : Ideles F →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

variable {F}

theorem infDiag_parts (k : Fˣ) : infPart F (infDiag k) = infPart F (diagUnits F k) ∧ finPart F (infDiag k) = 1 :=
  _root_.GlobalTheory.Mem.Chr.CharModel.infDiag_parts k

end Parts

section Product

variable {F : Type} [Field F] [NumberField F]


open Classical in
def cut (a : FiniteAdeleRing (𝓞 F) F) (T : Finset (HeightOneSpectrum (𝓞 F))) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ T then a v else 1, by
    refine Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun w hw => ?_)
    by_contra h
    apply hw
    have h' : w ∉ T := h
    simp only [h', ite_false]
    exact one_mem _⟩

theorem tendsto_cut (a : FiniteAdeleRing (𝓞 F) F) : Filter.Tendsto (cut a) Filter.atTop (nhds a) := by
  apply GlobalTheory.Mem.Chr.CharModel.tendsto_cut

theorem prod_local (k : Fˣ) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ((infDiag k * ∏ v ∈ T, localIdele F v (atFin v k) : Ideles F) : AdeleRing (𝓞 F) F) =
      (((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).1, cut ((diagUnits F k : Ideles F) : AdeleRing (𝓞 F) F).2 T) :=
  _root_.GlobalTheory.Mem.Chr.CharModel.prod_local k T

theorem tendsto_prod_local (k : Fˣ) :
    Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => infDiag k * ∏ v ∈ T, localIdele F v (atFin v k))
      Filter.atTop (nhds (diagUnits F k)) := by
  apply GlobalTheory.Mem.Chr.CharModel.tendsto_prod_local

theorem locK_unr (χ : HChar F) {v : HeightOneSpectrum (𝓞 F)} (h : χ.UnrAt v) (k : Fˣ) :
    χ.locK v k = χ.val v ^ ordF v k := by
  apply GlobalTheory.Mem.Chr.CharModel.locK_unr <;> assumption

theorem finite_ordF (k : Fˣ) : {v : HeightOneSpectrum (𝓞 F) | ordF v k ≠ 0}.Finite :=
  _root_.GlobalTheory.Mem.Chr.CharModel.finite_ordF k

theorem productRule (χ : HChar F) : χ.ProductRule := by
  apply GlobalTheory.Mem.Chr.CharModel.productRule

end Product

theorem hchar_productRule : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), χ.ProductRule :=
  fun _ _ _ χ => productRule χ

end GlobalTheory.HeckeProduct
