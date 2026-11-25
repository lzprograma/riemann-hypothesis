module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S
open scoped Classical

namespace GlobalTheory.LoopVol

variable {D : D7}

theorem root_fst_lt (w : Point D.host.E (D.R.rS + 1)) (q : GlobalTheory.LoopV.roots (ptMat w)) : q.1.1.1 < D.R.rS := by
  have hq := q.2
  simp only [GlobalTheory.LoopV.roots, Finset.mem_filter] at hq
  have h := hq.2.1
  have h2 := q.1.2.2
  rw [Fin.lt_def] at h
  omega

def ratCoord (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ s y : X.B.I.Ginf) : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ :=
  fun τ q => Formalism.L2.SG.HidaSetting.hJ (X.B.I.ε (X.pl.symm τ))
    (Formalism.L2.SG.HidaSetting.rv X.B.I (X.pl.symm τ) (X.fR ⟨q.1.1.1, root_fst_lt w q⟩))
    (uMat ((γ⁻¹ * (s⁻¹ * y * s) * γ) (X.pl.symm τ)) *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ) q.1.2)

theorem ratCoord_cont (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (γ s : X.B.I.Ginf) : Continuous (ratCoord X u' w γ s) := by
  unfold ratCoord Formalism.L2.SG.HidaSetting.hJ
  refine continuous_pi fun τ => continuous_pi fun q => ?_
  refine Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_const ?_)
  refine Continuous.matrix_mulVec ?_ continuous_const
  exact Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply _).comp
    ((continuous_const.mul ((continuous_const.mul continuous_id).mul continuous_const)).mul continuous_const)))

end GlobalTheory.LoopVol

end
