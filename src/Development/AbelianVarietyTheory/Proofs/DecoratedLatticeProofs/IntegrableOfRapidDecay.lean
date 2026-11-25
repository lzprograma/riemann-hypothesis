module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowSplit

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Rk.RapidInt

open scoped TensorProduct ENNReal NNReal ComplexConjugate Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Cont GlobalTheory.GaugeEx
open NumberField.mixedEmbedding
open scoped Classical

section Tup

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (M n : ℕ)

def crdTup : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₗ[Ainf F] (Fin n → Fin M → Fin d → Ainf F) :=
  LinearEquiv.piCongrRight fun _ => LinearEquiv.piCongrRight fun _ =>
    (Algebra.TensorProduct.basis (Ainf F) b).equivFun

def mixTup : (Fin n → Fin M → Fin d → Ainf F) ≃+ (Fin n → Fin M → Fin d → mixedSpace F) :=
  AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ =>
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv

theorem continuous_crdTup : Continuous (crdTup F E b M n) :=
  IsModuleTopology.continuous_of_linearMap (crdTup F E b M n).toLinearMap

theorem continuous_crdTup_symm : Continuous (crdTup F E b M n).symm :=
  IsModuleTopology.continuous_of_linearMap (crdTup F E b M n).symm.toLinearMap

theorem continuous_mixTup : Continuous (mixTup F M n (d := d)) :=
  continuous_pi fun a => continuous_pi fun i => continuous_pi fun k =>
    (PositivityTheory.ThKF0.Split.continuous_toMixed F).comp ((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply a)))

theorem continuous_mixTup_symm : Continuous (mixTup F M n (d := d)).symm :=
  continuous_pi fun a => continuous_pi fun i => continuous_pi fun k =>
    (PositivityTheory.ThKF0.Split.continuous_ofMixed F).comp ((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply a)))

def tupEquiv : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (Fin n → Fin M → Fin d → mixedSpace F) where
  toAddEquiv := (crdTup F E b M n).toAddEquiv.trans (mixTup F M n)
  continuous_toFun := (continuous_mixTup F M n).comp (continuous_crdTup F E b M n)
  continuous_invFun := (continuous_crdTup_symm F E b M n).comp (continuous_mixTup_symm F M n)


end Tup


end GlobalTheory.Core.Rk.RapidInt
