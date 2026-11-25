module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical

namespace GlobalTheory.RepLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem mem_iff_of_carries (y k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (N : Submodule (𝓞 E) (Fin n → E))
    (hN : Submodule.IsFullLattice E N) (h1 : Formalism.L2.Herm.Carries (y * k) (Formalism.L2.Col.stdLat E n) N)
    (h2 : Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n)) (x : Fin n → E) :
    x ∈ N ↔ ∀ i, (((y⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      fun j => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x j)) i ∈ Formalism.L2.Herm.intAf F E := by
  have hone := Formalism.UG.P.global_lattice_one_holds F E (Fin n) N (Module.Finite.iff_fg.mpr hN.fg) hN.span_eq_top
  have e0 : x ∈ N ↔ (fun j => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x j)) ∈ Formalism.L2.Herm.hatL (F := F) N := by
    conv_lhs => rw [← hone]
    show (((1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) N ↔ _
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  rw [e0, h1, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ← h2]
  exact Formalism.L2.Col.mem_latS_std _

theorem finM_mul' {D : D7} (V : HSp D) {m : ℕ} (hn : V.rank = m) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  change (Formalism.L2.Theta.mt V (g * h)).map (toEAf D) = (Formalism.L2.Theta.mt V g).map (toEAf D) * (Formalism.L2.Theta.mt V h).map (toEAf D)
  rw [← Matrix.map_mul]
  congr 1

theorem finM_one' {D : D7} (V : HSp D) {m : ℕ} (hn : V.rank = m) : finM V hn 1 = 1 := by
  subst hn
  change (Formalism.L2.Theta.mt V 1).map (toEAf D) = 1
  have e : Formalism.L2.Theta.mt V 1 = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one]
    rfl
  rw [e, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.RepLattice
