module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAdd
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.TChart.GensFrom

theorem lam_form {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {T : Over S} (x y : T ⟶ B) (U : Type)
    [CommGroup U] (H : (T.left ⟶ B.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), H ((lift x y).left ≫ (psum B (x2 B) I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      (∏ k, H (lamPts x y k) ^ negε k)⁻¹ := by
  have p : ∀ I : Finset (Fin 2), (lift x y).left ≫ (psum B (x2 B) I).left = (psum B ![x, y] I).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 B) I).trans (by
      congr 1; funext i; fin_cases i <;> simp [x2, preHom]))
  simp only [p]
  rw [← Equiv.ulift.symm.prod_comp, show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} from by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
    Fin.prod_univ_four]
  have q0 : psum B ![x, y] ∅ = 1 := rfl
  have q1 : psum B ![x, y] {0} = x := _root_.mul_one x
  have q2 : psum B ![x, y] {1} = y := _root_.mul_one y
  have q3 : psum B ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  simp [q0, q1, q2, q3, lamPts, negε]
  generalize H (x * y).left = A, H x.left = A₁, H y.left = A₂, H (1 : T ⟶ B).left = A₀
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart.GensFrom

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {F : Y' ⟶ Y}

theorem good_linComb {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good (LB.LinComb L φ ε) z (fun ψ k => J (ψ ≫ φ k)) := fun ψ => hJ.mem φ ψ

theorem val_flatGen (u : LB.Gen ((LB.LinComb L φ ε).pull F)) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : val (GlobalTheory.UU.flatGen u) r z J = val u r z (fun ψ k => J (ψ ≫ φ k)) := by
  exact (gm_res r z _ (hJ.mem (fun k => F ≫ φ k) r) _).trans
    (val_of u r z _ (fun _ k => J (r ≫ F ≫ φ k)) (fun _ => funext fun k => by simp only [Category.assoc])).symm

theorem val_unflatGen (v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : val (GlobalTheory.UU.unflatGen v) r z (fun ψ k => J (ψ ≫ φ k)) = val v r z J := by
  exact (gm_res r z _ ((good_linComb (φ := φ) (ε := ε) hJ).mem (fun _ : PUnit => F) r) _).trans
    (val_of v r z J (fun k => J ((r ≫ F) ≫ φ k)) (fun k => by simp only [Category.assoc])).symm

end GlobalTheory.TChart.GensFrom

namespace GlobalTheory.TChart.GensFrom

theorem om_lam {S S' : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B']
    {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left} (w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂))
    {Z : Scheme.{0}} (p : Z ⟶ (G2 B').left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J' : (Z ⟶ B'.left) → M'.ι) :
    GlobalTheory.ArcPull.om w z (fun ψ (I : ULift.{0} (Finset (Fin 2))) => J (ψ ≫ (psum B (x2 B) I.down).left))
      (fun ψ (I : ULift.{0} (Finset (Fin 2))) => J' (ψ ≫ (psum B' (x2 B') I.down).left)) p = lamVal w p z J J' := by
  have H : ∀ i i' : (LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).ι, i = i' →
      gm p z ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U i) (w.s i) =
        gm p z ((LB.div ((abelian₂ B M).pull β₂) (abelian₂ B' M')).U i') (w.s i') := by
    rintro _ _ rfl; rfl
  unfold GlobalTheory.ArcPull.om Geo.Tor.gw lamVal
  refine H (fun _ (I : ULift.{0} (Finset (Fin 2))) => J ((p ≫ β₂) ≫ (psum B (x2 B) I.down).left),
      fun (I : ULift.{0} (Finset (Fin 2))) => J' (p ≫ (psum B' (x2 B') I.down).left))
    (fun _ (I : ULift.{0} (Finset (Fin 2))) => J (p ≫ β₂ ≫ (psum B (x2 B) I.down).left),
      fun (I : ULift.{0} (Finset (Fin 2))) => J' (p ≫ (psum B' (x2 B') I.down).left)) (Prod.ext ?_ rfl)
  funext _ I
  exact congrArg J (Category.assoc _ _ _)

end GlobalTheory.TChart.GensFrom
