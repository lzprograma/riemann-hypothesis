module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem exists_cancel_of_eq {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X}
    {F' : X'' ⟶ X'} {F'' : X'' ⟶ X} (e : F' ≫ F = F'') (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB)
    (w : LB.Iso L' (L.pull F)) (w'' : LB.Iso L'' (L.pull F'')) (hw : PGen w) (hw'' : PGen w'')
    {Y Y' Y'' : Scheme.{0}} {φ : Y ⟶ X} {φ' : Y' ⟶ X'} {φ'' : Y'' ⟶ X''}
    {t : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => 1))}
    {t' : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => φ') (fun _ => 1))}
    {t'' : LB.Gen (LB.LinComb L'' (K := PUnit) (fun _ => φ'') (fun _ => 1))}
    {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'} {h'' : Y'' ⟶ Y} (eh : h' ≫ h = h'') (hc : φ'' ≫ F' = h' ≫ φ')
    (H : PMaps w _ _ _ t' t h) (H'' : PMaps w'' _ _ _ t'' t h'') :
    ∃ w' : LB.Iso L'' (L'.pull F'), PGen w' ∧ PMaps w' _ _ _ t'' t' h' ∧
      ∀ (Z : Scheme.{0}) (z : Z) J J' J'', Good L z J → Good L' z J' → Good L'' z J'' → ∀ x : Z ⟶ X'',
        om w'' z J J'' x = om w z J J' (x ≫ F') * om w' z J' J'' x := by
  subst e eh
  obtain ⟨w', T⟩ := exists_cancel hL w w'' hw hw'' hL' hL''
  refine ⟨w', T.pgen_cancel hL hw hw'', T.pmaps_cancel hL (fun _ => hc) H H'', fun Z z J J' J'' hJ hJ' hJ'' x => ?_⟩
  rw [om, om, om, Category.assoc]
  exact T Z x z _ _ _ (hJ (x ≫ F' ≫ F)) (hJ' (x ≫ F')) (hJ'' x)

theorem exists_isPullDeg_cancel : ∀ (K₀ K₁ K : Type) [Field K₀] [Field K₁] [Field K] (α : K₀ →+* K₁) (β : K₁ →+* K) (D₀ : DegPre K₀) (D₁ : DegPre K₁) (D : DegPre K) (h₁ : IsPullDeg α D₀ D₁) (h : IsPullDeg (β.comp α) D₀ D), ∃ hD : IsPullDeg β D₁ D, PsiEvenPull.proj hD ≫ PsiEvenPull.proj h₁ = PsiEvenPull.proj h := by
  intro K₀ K₁ K _ _ _ α β D₀ D₁ D h₁ h
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w ((isGen_iff _).1 h₁.w_gen)
    ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (pmaps_rig h₁) (pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨hD, hΦ, -, -⟩ := exists_isPullDeg_of_val β D₁ D gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK K ≫ spMap β = genMap β.injective ≫ jK K₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq β.injective)
    have sα : jK K₁ ≫ spMap α = genMap α.injective ≫ jK K₀ :=
      (Category.id_comp _).symm.trans (fracMap_sq α.injective)
    have q₁ : genMap β.injective ≫ jK K₁ ≫ spMap α = (genMap β.injective ≫ genMap α.injective) ≫ jK K₀ :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK K).left ≫ jK K ≫ spMap (β.comp α) = (genMap β.injective ≫ genMap α.injective) ≫ jK K₀ :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap β.injective ≫ D₁.xK (xe x) := by
      show (jK K ≫ (D.c x).left) ≫ Φ = genMap β.injective ≫ jK K₁ ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD, hΦ ▸ e₁⟩

end GlobalTheory.FieldPull
end
