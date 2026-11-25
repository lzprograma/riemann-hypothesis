module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LamXEquivariant
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NearLowerCompare

open Formalism.MainNotions.S GlobalTheory.Count Formalism.HN

variable (I : AutInst)

theorem lamX_isLattice (x : I.GA) : Submodule.IsLattice I.E (lamX I x) := by
  have h := Formalism.UG.P.global_lattice_isLattice_holds I.F I.E (Fin I.n) I.L (Module.Finite.iff_fg.2 I.L_fg) I.L_span
    (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
  have e1 : Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L = I.Lf := by
    unfold Formalism.UG.latS AutInst.Lf lamAf
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩; exact ⟨z, z.2, rfl⟩
  have e : lamX I x = Formalism.UG.CS.globLat (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) I.L := by
    ext y
    rw [GlobalTheory.Count.Test.mem_lamX, ← e1]
    exact Iff.rfl
  rw [e]; exact h

theorem frm_isUnit (x : I.GA) (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  have h : ∀ v, IsUnit (I.P v * uMat (x.1 v)) := fun v => (I.P_unit v).mul (Units.isUnit _)
  rw [← Matrix.isUnit_iff_isUnit_det]
  unfold frm
  split_ifs
  · exact h _
  · exact (h _).map (starRingEnd ℂ).mapMatrix

theorem subsingleton_GA (hn : I.n = 0) : Subsingleton I.GA := by
  have : IsEmpty (Fin I.n) := by rw [hn]; infer_instance
  refine ⟨fun a b => Prod.ext (funext fun v => ?_) ?_⟩
  · exact Subtype.ext (Units.ext (Subsingleton.elim _ _))
  · exact Subtype.ext (Units.ext (Subsingleton.elim _ _))

end GlobalTheory.NearLowerCompare
