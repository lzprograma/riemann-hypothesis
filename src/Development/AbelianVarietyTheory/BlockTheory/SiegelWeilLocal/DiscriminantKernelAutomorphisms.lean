module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open scoped Classical

namespace GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

section Row

variable (D : D7)

def sumMap {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) :
    ((D.sp.X 0).V × D.host.E) →ₗ[D.host.E] (VS D).V :=
  (D.sp.iXY 0).coprod (LinearMap.toSpanSingleton D.host.E (VS D).V F0.z)

def latL {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) :
    Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E) :=
  (Lsub Λ (lf D F0)).comap ((sumMap D F0).restrictScalars (𝓞 D.host.E))

abbrev flagPairDefinitePartLattice {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) :
    Submodule (𝓞 D.host.E) (D.sp.X 0).V :=
  L0X D Λ (lf D F0)

end Row

theorem mem_orthModIsotropicLatticePerpNegative_iff (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (hz : F0.z = D.zmOf u) (Λ : LatV D) (w : (D.sp.X 0).V) :
    w ∈ flagPairDefinitePartLattice D F0 Λ ↔ (w, (0 : D.host.E)) ∈ latL D F0 Λ := by
  have h0 : (VS D).hT F0.z (D.sp.iXY 0 w) = 0 := by
    have h1 : (VS D).hT (D.sp.iXY 0 w) F0.z = 0 := by
      rw [hz, D7.zmOf, map_smul, D.sp.zm_orth w, smul_zero]
    have h2 := (VS D).herm.eq (D.sp.iXY 0 w) F0.z
    rw [h1, map_zero] at h2
    exact h2.symm
  simp [flagPairDefinitePartLattice, L0X, L0sub, latL, sumMap, h0]

end GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms

end
