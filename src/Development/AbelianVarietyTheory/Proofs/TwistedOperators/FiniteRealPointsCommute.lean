module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
open scoped TensorProduct

namespace GlobalTheory.FinRealComm

private theorem eq_map_inl_fst_add_map_inr_snd_tmul {F A B E : Type} [CommRing F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (z : (A × B) ⊗[F] E) :
    z = TensorProduct.map (LinearMap.inl F A B) LinearMap.id
          (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
        TensorProduct.map (LinearMap.inr F A B) LinearMap.id
          (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.map_tmul, ← TensorProduct.add_tmul]
    congr 1
    ext <;> simp
  | add u v hu hv =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]
    conv_lhs => rw [hu, hv]
    abel

theorem tensor_prod_ext {F A B E : Type} [CommRing F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (x y : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) y)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) y) : x = y := by
  rw [eq_map_inl_fst_add_map_inr_snd_tmul x, eq_map_inl_fst_add_map_inr_snd_tmul y, h1, h2]

theorem GA_ext_inf_fin {D : D7} (V : HSp D) (x y : GA D V)
    (h1 : infHom V x = infHom V y) (h2 : finHom V x = finHom V y) : x = y := by
  have hm : (matHom V x).1 = (matHom V y).1 := by
    ext i j
    have e1 := congrArg (fun g => g.1 i j) h1
    have e2 := congrArg (fun g => g.1 i j) h2
    simp only [infHom, finHom, MonoidHom.comp_apply, Formalism.UG.bc, Units.coe_map,
      MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at e1 e2
    exact tensor_prod_ext _ _ e1 e2
  exact Subtype.ext (Units.ext hm)

theorem finite_real_points_commute :
    ∀ {D : D7} (V : HSp D) (a b : GA D V), a ∈ GfC V → b ∈ GinfC V → a * b = b * a := by
  intro D V a b ha hb
  have ha' : infHom V a = 1 := ha
  have hb' : finHom V b = 1 := hb
  apply GA_ext_inf_fin V
  · rw [map_mul, map_mul, ha', one_mul, mul_one]
  · rw [map_mul, map_mul, hb', one_mul, mul_one]

end GlobalTheory.FinRealComm
