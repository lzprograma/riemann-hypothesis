module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw

namespace GlobalTheory.EtaTildeOfComponents

theorem isEtaTilde_of_chrEq : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (η : (AE D)ˣ →* Circle), ChrEq η C.eta → ResEta D η 1 → IsEtaTilde D η := by
  intro D C η hc hres
  have hE := C.isEta

  have hInf : C.eta.HasInfQ (tauE D) (fun _ => (1 / 2 : ℚ)) := by
    refine ⟨fun _ => 1, fun _ => by norm_num, fun k => ?_⟩
    rw [hE.inf k]
    exact (Fintype.prod_equiv D.eTau _ _ (fun _ => rfl)).symm
  have h1 : 1 ∈ intAE D := by
    apply AddSubgroup.subset_closure
    refine ⟨1, fun v => ?_, 1, rfl⟩
    simp [evalV, (v.adicCompletionIntegers D.host.F).one_mem]
  refine ⟨hc.1, ?_, hres, fun τ => GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D η C.eta _ hc hInf τ⟩

  intro x hx1 hx2 hx3
  refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D η C.eta hc ?_ 1 (fun P _ => hE.unr P) x ⟨hx1, hx2, hx3⟩
    ⟨finPart D (x : AE D) - 1, sub_mem hx2 h1, (one_nsmul _).symm⟩
  intro P y hy _
  exact hE.unr P y hy

end GlobalTheory.EtaTildeOfComponents
