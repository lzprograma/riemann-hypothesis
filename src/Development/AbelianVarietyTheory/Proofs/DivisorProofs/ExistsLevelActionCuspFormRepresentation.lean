module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
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

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct

namespace GlobalTheory.LevelRep



theorem exists_cusp_rep : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → (∀ g, ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev T.Q.c lev g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) → ∃ ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i), ∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) := by
  intro D G _ T κ i lev _ hL hW
  have hnat := fun f (hf : f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) => ((mem_cusp _ _ _ _ _ _).1 hf).1.1
  exact ⟨{ toFun := fun g => (actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev g).restrict (hW g)
           map_one' := LinearMap.ext fun F => Subtype.ext
             (actL_one _ _ _ hL.total hL.func hL.one (hnat _ F.2))
           map_mul' := fun g g' => LinearMap.ext fun F => Subtype.ext
             (actL_mul _ _ _ hL.total hL.func hL.mul g g' (hnat _ F.2)) },
    fun _ _ => rfl⟩

end GlobalTheory.LevelRep
