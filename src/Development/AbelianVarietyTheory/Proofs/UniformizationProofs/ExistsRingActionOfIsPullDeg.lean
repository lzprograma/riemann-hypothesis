module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalOfIsPullDeg
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_oAct_of_isPullDeg : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] (ιD : D.OAct O), ∃ (_ : Module O D'.X) (ιD' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) ∧ (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) := by
  intro hG R R' _ _ _ _ φ D D' hD O _ _ _ ιD
  have gp := pull_grp hD
  obtain ⟨o', ho'⟩ := polOActPull _ _ _ D.P D'.P _ gp (LBIso.symm ⟨hD.w, hD.w_gen⟩) O ιD.onB
  letI inst : Module O D'.X := hD.xe.module O
  have hs : ∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y := fun a y =>
    hD.xe.apply_symm_apply _
  have he : ∀ a, o'.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a) := fun a => by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · have := ho' a
      simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst] at this ⊢
      exact this
    · exact (Over.w (o'.act a ≫ hD.e.hom)).trans
        (Over.w (hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a))).symm
  refine ⟨inst, ⟨o', fun a y => ?_, fun a => ?_⟩, hs, he⟩
  · refine Over.OverMorphism.ext (gp.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [hD.c_pr, hs, ιD.c_lin, Over.comp_left, Over.comp_left, Category.assoc, ho', ← Category.assoc,
      ← Category.assoc (D'.c y).left, hD.c_pr]
  · exact tauBal_of_isPullDeg hG R R' φ D D' hD _ _ _ _ (ιD.onB.hom a) (ιD.onB.hom (star a)) (ιD.onB.rosati a)
      (he a) (he (star a)) _ _ _ _ (hs a) (hs (star a)) (ιD.c_lin a) (ιD.c_lin (star a)) (ιD.tau_bal a)

end GlobalTheory
