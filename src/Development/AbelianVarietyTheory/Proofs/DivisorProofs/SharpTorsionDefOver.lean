module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionIsoOfGroupPullbackGeneric
import Mathlib.Tactic.Linter.Style
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

theorem exists_points_equiv {W₀ : Type} [CommRing W₀] (ρ : V →+* V₁) (ib : W₀ →+* V) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)),
      ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.B.left ⟶ B₀.left) (hβ : IsGrpPullback Q.B B₀ (spMap ib) β)
    {X : Scheme.{0}} (t : X ⟶ Sp V₁) (g : X ⟶ Sp W₀) (hg : t ≫ spMap ρ ≫ spMap ib = g) :
    ∃ Φ : (Over.mk t ⟶ D.P.A) ≃* (Fin 8 → (Over.mk g ⟶ B₀)),
      ∀ x a, (Φ x a).left = x.left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β := by
  obtain ⟨E1, hE1⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback
    (isGrpPullback_pullback Q.B (spMap ρ)) t (t ≫ spMap ρ) rfl
  obtain ⟨E2, hE2⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (t ≫ spMap ρ) g
    (by rw [Category.assoc]; exact hg)
  let P : (Over.mk t ⟶ D.P.A) →* (Fin 8 → (Over.mk t ⟶ (Over.pullback (spMap ρ)).obj Q.B)) :=
    Pi.monoidHom fun a =>
      { toFun := fun x => x ≫ pr a
        map_one' := MonObj.one_comp _
        map_mul' := fun x y => MonObj.mul_comp _ _ _ }
  have hP : Function.Bijective P := by
    refine ⟨fun x y h => ?_, fun y => ?_⟩
    · obtain ⟨z, -, hz⟩ := huniv (Over.mk t) (P x)
      exact (hz x fun a => rfl).trans (hz y fun a => (congrFun h a).symm).symm
    · obtain ⟨z, hz, -⟩ := huniv (Over.mk t) y
      exact ⟨z, funext hz⟩
  refine ⟨(MulEquiv.ofBijective P hP).trans (MulEquiv.piCongrRight fun _ => E1.trans E2), fun x a => ?_⟩
  show (E2 (E1 (x ≫ pr a))).left = _
  rw [hE2, hE1, Over.comp_left]
  simp only [Category.assoc]

theorem spMap_three {A B C E : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing E] (f : A →+* B) (g : B →+* C)
    (h : C →+* E) : spMap h ≫ spMap g ≫ spMap f = spMap ((h.comp g).comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

end GlobalTheory.Poinc.Sep
