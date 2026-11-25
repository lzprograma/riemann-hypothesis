module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnitaryAdelicLocalComponentsContinuousLevelsOpen
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem isOpen_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsOpen (globLev S K' : Set (finU (E := E) (n := n))) := by
  intro E _ _ _ hU n S K' hK
  have hT : {w : Pl E | ¬ K' w = KL n w}.Finite := Filter.eventually_cofinite.1 hK.2
  let f : ∀ w : Pl E, finU (E := E) (n := n) → UL n w := fun w x => ⟨cLoc w x.1, GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w x.1⟩
  have hf : ∀ w, Continuous (f w) := fun w =>
    Continuous.subtype_mk ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val) _
  have h1 : ∀ w, f w 1 = 1 := fun w => Subtype.ext (by simp [f])
  have hA : ∀ᶠ k : finU (E := E) (n := n) in nhds 1, ∀ w : Pl E, cLoc w (k : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    filter_upwards [(UpperTheory.unitaryAdelic_localComponents_continuous_levels_open E n).2.2] with k hk w
    exact (SetLike.ext_iff.1 (GlobalTheory.SmGL.SphCompletion.KO_completion w n) _).1 (hk w)
  have hB : ∀ᶠ k : finU (E := E) (n := n) in nhds 1, ∀ w ∈ {w : Pl E | ¬ K' w = KL n w}, f w k ∈ K' w := by
    refine (Filter.eventually_all_finite hT).2 fun w _ => ?_
    have ho : IsOpen ((f w) ⁻¹' (K' w : Set (UL n w))) := ((hK.1 w).1).preimage (hf w)
    exact ho.mem_nhds (by simp [h1])
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [hA, hB] with x hxA hxB
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun _ => ?_
  refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨f w x, ?_, rfl⟩)
  by_cases hw : K' w = KL n w
  · rw [hw]
    exact Subgroup.mem_subgroupOf.2 (hxA w)
  · exact hxB w hw

end GlobalTheory.BCT
