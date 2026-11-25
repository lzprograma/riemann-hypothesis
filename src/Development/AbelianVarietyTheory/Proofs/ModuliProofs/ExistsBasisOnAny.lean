module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.PushInv

open LBGerm

theorem exists_basisOn_any {S : Scheme.{0}} (hS : SecBaseChangeAnySt) (P : PolAV S) (x : S) :
    ∃ V : S.Opens, x ∈ V ∧ ∃ θ ∈ secOn P.L (P.A.hom ⁻¹ᵁ V), IsBasisOn P.A P.L V θ :=
  exists_basisOn_of_secBaseChangeAt (hS S P 1 le_rfl x)

theorem pushInvertible_any : Out.SecBaseChangeAnySt → Out.GlobalSectionsRankAlgClosed →
    ∀ (S : Scheme.{0}) (Q : Out.PolAV S), PushInvertible Q.A Q.L := by
  intro hS _ S P x
  obtain ⟨V, hV, θ, hθ, H⟩ := exists_basisOn_any hS P x
  haveI := P.smoothDim
  haveI : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  refine ⟨V, hV, θ, hθ, fun W hW s hs => ?_, exists_nonvanishing H⟩
  have e : ∀ (a : Γ(S, W)) (g : P.A.left) i, P.A.hom g ∈ W → g ∈ P.L.U i →
      gs (𝟙 _) g _ ((P.A.hom.appLE W (P.A.hom ⁻¹ᵁ W ⊓ P.L.U i) inf_le_left).hom a *
        resG P.A.left (inf_le_inf_right _ (P.A.hom.preimage_mono hW)) (θ i)) =
      gs P.A.hom g W a * gs (𝟙 _) g _ (θ i) := fun a g i hg hi => by
    have hm : g ∈ P.A.hom ⁻¹ᵁ W ⊓ P.L.U i := ⟨hg, hi⟩
    rw [gs_mul (𝟙 _) g _ hm, gs_res (𝟙 _) g _ hm, gs_appLE _ _ _ _ (𝟙 _) g hm, Category.id_comp]
  obtain ⟨a, ha⟩ := exists_coeff H hW hs
  refine ⟨a, fun i => fn_ext fun g hg => (ha g i hg.1 hg.2).trans (e a g i hg.1 hg.2).symm, fun a' ha' => ?_⟩
  exact eq_of_mul H hW _ _ fun g i hg hi =>
    ((e a' g i hg hi).symm.trans (congrArg _ (ha' i).symm)).trans (ha g i hg hi)

end GlobalTheory.PushInv
