module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
open Classical

namespace GlobalTheory.SeeSaw.RealComm

variable {D : D7}

theorem map_mul_gen {A B m n : Type} [CommRing A] [CommRing B] [Fintype n] (φ : A →+* B) (u : Matrix m n A) (g : Matrix n n A) :
    (u * g).map φ = u.map φ * g.map φ := Matrix.map_mul

theorem actO_real_fin (S T : HSp D) {z : GA D S} (hz : z ∈ GinfC S) {u : WO S T} (hu : u.map (infPart D) = 0) :
    actO S T z 1 u = u := by
  have h1 : Formalism.L2.Theta.mt T 1 = 1 := rfl
  have hz' : finHom S z⁻¹ = 1 := (GinfC S).inv_mem hz
  have h2 : (Formalism.L2.Theta.mt S z⁻¹).map (finPart D) = 1 := congrArg Units.val hz'
  rw [actO, h1, Matrix.one_mul]
  have h3 := map_mul_gen (finPart D) u (Formalism.L2.Theta.mt S z⁻¹)
  have h4 := map_mul_gen (infPart D) u (Formalism.L2.Theta.mt S z⁻¹)
  rw [h2, Matrix.mul_one] at h3
  rw [hu, Matrix.zero_mul, ← hu] at h4
  exact Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext (congrFun (congrFun h4 i) j) (congrFun (congrFun h3 i) j)

theorem om_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ z ∈ GinfC S, ∀ c : WO S T →₀ ℂ, IsFinComb c → ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → om (z, 1) (comb ψ S T c g) = comb ψ S T c (om (z, 1) g) := by
  intro D ψ S T χS χT om H z hz c hc g hg
  unfold comb

  rw [map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [map_smul, H.om_heis z 1 u g hg, actO_real_fin S T hz (hc u hu)]

end GlobalTheory.SeeSaw.RealComm
