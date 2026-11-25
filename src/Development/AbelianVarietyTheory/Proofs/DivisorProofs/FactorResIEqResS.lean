module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace GlobalTheory.GeoActCompare

open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

section Res

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def resI (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) : Formalism.L2.Herm.intAf F E →+* 𝓞 E ⧸ I :=
  ((RingEquiv.ofBijective (cmpS F I) (cmpS_bij (F := F) I hI)).symm : _ →+* 𝓞 E ⧸ I).comp
    (Ideal.Quotient.mk (idS F I))

variable {F}

theorem resI_oToS (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (a : 𝓞 E) :
    resI F I hI (oToS F E a) = Ideal.Quotient.mk I a := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F I) _).symm _ = _
  rw [RingEquiv.symm_apply_eq]
  rfl

theorem resI_eq_zero_iff (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (s : Formalism.L2.Herm.intAf F E) :
    resI F I hI s = 0 ↔ s ∈ idS F I := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F I) _).symm _ = _ ↔ _
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

theorem resS_eq_resI (w : Pl E) : resS F w = resI F w.asIdeal w.ne_bot := rfl

end Res

end GlobalTheory.GeoActCompare
