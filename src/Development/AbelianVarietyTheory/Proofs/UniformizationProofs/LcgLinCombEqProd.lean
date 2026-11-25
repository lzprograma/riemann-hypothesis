module

import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullGenBoxGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

namespace GlobalTheory

lemma boxGen_overlap_le {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (a b : K → (LB.LinComb L F (fun _ => 1)).ι) (i : J) :
    LB.wchart (LB.LinComb L F (fun _ => 1)) φ a ⊓ LB.wchart (LB.LinComb L F (fun _ => 1)) φ b ≤
      LB.wchart (L.pull (F i)) φ (fun k _ => a k i) ⊓
        LB.wchart (L.pull (F i)) φ (fun k _ => b k i) := by
  have key : ∀ c : K → (LB.LinComb L F (fun _ => 1)).ι,
      LB.wchart (LB.LinComb L F (fun _ => 1)) φ c ≤ LB.wchart (L.pull (F i)) φ (fun k _ => c k i) := by
    intro c y hy
    simp only [LB.wchart, LB.pull, LB.LinComb, TopologicalSpace.Opens.mem_mk, Set.mem_iInter,
      Set.mem_preimage, SetLike.mem_coe] at hy ⊢
    intro k _
    exact hy k i
  exact inf_le_inf (key a) (key b)

lemma lcg_linComb_eq_prod {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (a b : K → (LB.LinComb L F (fun _ => 1)).ι) :
    LB.lcg (LB.LinComb L F (fun _ => 1)) φ ε a b =
      ∏ i, res (boxGen_overlap_le L F φ a b i)
        (LB.lcg (L.pull (F i)) φ ε (fun k _ => a k i) (fun k _ => b k i)) := by
  show (∏ k, (res _ (pullU (φ k) (LB.wchart L F (a k) ⊓ LB.wchart L F (b k))
      (LB.lcg L F (fun _ => 1) (a k) (b k)))) ^ ε k) =
    ∏ i, res _ (∏ k, (res _ (pullU (φ k)
      (LB.wchart L (fun _ : PUnit => F i) (fun _ => a k i) ⊓ LB.wchart L (fun _ : PUnit => F i) (fun _ => b k i))
      (LB.lcg L (fun _ : PUnit => F i) (fun _ => 1) (fun _ => a k i) (fun _ => b k i)))) ^ ε k)
  simp only [LB.lcg, map_prod, map_zpow, zpow_one, Finset.univ_unique, Finset.prod_singleton,
    ReciprocityTheory.ChartRestriction.G.DVR.pullU_res, ← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
  congr 1
  repeat erw [ReciprocityTheory.ChartRestriction.G.DVR.res_res']

theorem isGen_boxGen {X X' Y : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]
    (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (ht : ∀ i, (t i).IsGen) :
    (GeneratorPullback.boxGen L F φ ε t).IsGen := by
  apply GlobalTheory.BoxCubical.isGen_boxGen <;> assumption

theorem boxIsLB (S : Scheme.{0}) : BoxIsLBSt (S := S) := by
  intro G' G _ _ j p L hL
  exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _

theorem boxRigIsGen (S : Scheme.{0}) : BoxRigIsGenSt (S := S) := by
  intro G' G _ _ _ _ j p L r hL hr
  refine isGen_boxGen _ _ _ _ _ (fun i => ?_)
  have := p.hom i
  exact LBxP.isGen_pullAlong L (p.pr i).left (𝟙 _) (fun _ : PUnit => eSec G)
    (fun _ => 1) (fun _ => eSec G') (fun _ => (CubeMap.ofHom (p.pr i)).e_comm) r hr

end GlobalTheory
