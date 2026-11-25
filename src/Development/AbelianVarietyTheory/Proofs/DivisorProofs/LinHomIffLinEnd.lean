module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumFam

variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R']

abbrev pol {I : Ideal R} (D : DegData R I) : Data R := Wit.ofDeg D.toPre D.tau_bimult

def RefAt (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (β : D.P.A.left ⟶ Q.B.left) : Prop :=
  letI := D.P.isAb.comm
  ∃ (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)),
    IsGrpPullback D.P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) ∧
    ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.tau a b) (𝟙 _) z J' =
        lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J

def TorusHomOf {S : Scheme.{0}} {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂] (h : X₂ → X₁)
    (t : splitTorus S X₁ ⟶ splitTorus S X₂) : Prop :=
  ∀ χ : X₂, res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X₂ χ)) = charUnit S X₁ (h χ)

variable {I : Ideal R} {D₁ D₂ D₃ : DegData R I} {A₁ A₂ A₃ : PolAV (Sp (FractionRing R))} {G₁ G₂ G₃ : Over (Sp R)}
  [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] [GrpObj G₃] [IsCommMonObj G₃]

def LinHom (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : D₁.toPre.P.A ⟶ D₂.toPre.P.A)
    (h' : D₂.toPre.X →+ D₁.toPre.X) (g : G₁ ⟶ G₂) : Prop :=
  IsMonHom g ∧ (∀ e, (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map a) ∧
    ∀ e, ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
      TorusHomOf h' t ∧ (U₁.gt e).i ≫ (Over.pullback (thick R I e)).map g = t ≫ (U₂.gt e).i

theorem TorusHomOf.comp {S : Scheme.{0}} {X₁ X₂ X₃ : Type} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    {h : X₂ → X₁} {k : X₃ → X₂} {t : splitTorus S X₁ ⟶ splitTorus S X₂} {s : splitTorus S X₂ ⟶ splitTorus S X₃}
    (ht : TorusHomOf h t) (hs : TorusHomOf k s) : TorusHomOf (fun χ => h (k χ)) (t ≫ s) := fun χ => by
  rw [← ht (k χ), ← hs χ]
  refine unit_ext fun z _ => ?_
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_
  refine Eq.symm (((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_)
  refine ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull _ _ z ⊤ trivial _)).trans ?_
  rfl

theorem TorusHomOf.id {S : Scheme.{0}} (X : Type) [AddCommGroup X] : TorusHomOf (fun χ : X => χ) (𝟙 (splitTorus S X)) :=
  fun χ => unit_ext fun z _ =>
    ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans rfl

theorem LinHom.id (U : UnifPre I D₁ A₁ G₁) : LinHom U U (𝟙 _) (AddMonoidHom.id _) (𝟙 G₁) :=
  ⟨inferInstance, fun e => by simp, fun e => ⟨𝟙 _, TorusHomOf.id _, by simp⟩⟩

theorem LinHom.comp {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂} {U₃ : UnifPre I D₃ A₃ G₃} {a h' g b k' f}
    (hg : LinHom U₁ U₂ a h' g) (hf : LinHom U₂ U₃ b k' f) : LinHom U₁ U₃ (a ≫ b) (h'.comp k') (g ≫ f) := by
  obtain ⟨g₁, g₂, g₃⟩ := hg
  obtain ⟨f₁, f₂, f₃⟩ := hf
  refine ⟨inferInstance, fun e => ?_, fun e => ?_⟩
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, f₂, ← Category.assoc, g₂, Category.assoc]
  · obtain ⟨t, ht, hi⟩ := g₃ e
    obtain ⟨s, hs, hj⟩ := f₃ e
    refine ⟨t ≫ s, ht.comp hs, ?_⟩
    rw [Functor.map_comp, ← Category.assoc, hi, Category.assoc, hj, Category.assoc]

end GlobalTheory.MumFam
