module

import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellFin
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Formalism.PeriodIntegrals.ScPsiExists

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace

noncomputable section

namespace GlobalTheory.St.G

theorem trace_cm_eq_add_star {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + star x := by
  first | exact _root_.Formalism.MainNotions.BridgeLemma.tie_trace | exact @_root_.Formalism.MainNotions.BridgeLemma.tie_trace | apply _root_.Formalism.MainNotions.BridgeLemma.tie_trace <;> assumption

theorem psiEinf_eq_exp_trace (I : Formalism.MainNotions.S.AutInst) (y : I.E) :
    psiEinf I y = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ I.E y : ℚ) : ℂ)) := by
  have := I.cm.totReal
  rw [show psiEinf I y = PI.ScPsiExists.psiEinf I y from rfl, PI.ScPsiExists.UnitaryGroupMassFormula.psiEinf_eq,
    PI.ScPsiExists.UnitaryGroupMassFormula.sHom_coe]
  have h2 : ∀ v, I.φ v y + star (I.φ v y) =
      v.embedding (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed y) := by
    intro v
    rw [← I.φ_over, PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, map_add (f := _), I.cm.cmUnram.2.1 (I.φ v) y]
    rfl
  have h3 : PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed y = Algebra.trace I.F I.E y := by
    apply (algebraMap I.F I.E).injective
    rw [PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, trace_cm_eq_add_star I.cm]
  rw [Finset.sum_congr rfl (fun v _ => h2 v), PI.ScPsiExists.UnitaryGroupMassFormula.sum_embedding_eq_trace, h3,
    Algebra.trace_trace]
  rfl

theorem psiEf_transport_rat : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ x : D.host.E, X.psiEf (ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x)) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ)) = 1 := by
  intro D X ιA hA x
  have h1 : ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm x) := by
    rw [RingEquiv.symm_apply_eq, hA.1 (X.ιE.symm x), X.ιE.apply_symm_apply]
  have htr : Algebra.trace ℚ D.host.E x = Algebra.trace ℚ X.B.I.E (X.ιE.symm x) := by
    conv_lhs => rw [← X.ιE.apply_symm_apply x]
    exact Algebra.trace_eq_of_algEquiv X.ιE.toRatAlgEquiv (X.ιE.symm x)
  rw [h1, htr, ← psiEinf_eq_exp_trace]
  exact X.psiEf_rat (X.ιE.symm x)

end GlobalTheory.St.G

end
