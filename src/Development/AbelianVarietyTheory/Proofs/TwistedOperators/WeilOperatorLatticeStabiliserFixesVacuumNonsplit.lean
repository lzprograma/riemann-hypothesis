module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorFixesLatticeVacuumNonsplitUnramified
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFixesVacuumNonSplitPlaceUnramifiedStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct

namespace GlobalTheory.VecInvInert

variable {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
  {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}

theorem idem_smul_eq (hε : IsPlaceIdem D v ε) {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v) :
    algebraMap (AF D.host.F) (AE D) ε • u = u := by
  first | exact _root_.GlobalTheory.InertVac.placeIdem_smul_eq | exact @_root_.GlobalTheory.InertVac.placeIdem_smul_eq | apply _root_.GlobalTheory.InertVac.placeIdem_smul_eq <;> assumption

theorem mem_place_iff (hε : IsPlaceIdem D v ε) (u : WO S T) :
    u ∈ (latO S T LS LT fun w => w = v) ↔
      u ∈ (latO S T LS LT fun _ => True) ∧ algebraMap (AF D.host.F) (AE D) ε • u = u := by
  exact GlobalTheory.InertVac.mem_latO_place_iff hε u

theorem act_injective (g : GA D S) (h : GA D T) : Function.Injective (actO S T g h) := by
  first | exact _root_.GlobalTheory.InertVac.actO_injective | exact @_root_.GlobalTheory.InertVac.actO_injective | apply _root_.GlobalTheory.InertVac.actO_injective <;> assumption

theorem om_fixes_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ η, IsEtaTilde D η) → ∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → ∀ g h, SuppPl ε S g → SuppPl ε T h → (∀ u, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ actO S T g h u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → om (g, h) f = f := by
  intros
  apply _root_.GlobalTheory.InertVac.om_fixes_latVac <;> assumption

end GlobalTheory.VecInvInert

end
