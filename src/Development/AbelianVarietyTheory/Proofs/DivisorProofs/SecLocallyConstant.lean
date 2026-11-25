module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Topology.DiscreteQuotient
public import Mathlib.Topology.LocallyConstant.Algebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleModuleSheafSectionsCoprodBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsModuleCatIffForgetIffElStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiCofanIsColimitOfRingEquiv

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LCSec

variable (X : Type) [TopologicalSpace X] (B : Type) [CommRing B]

def preQ {S T : DiscreteQuotient X} (h : T ≤ S) : (S → B) →+* (T → B) where
  toFun g t := g (DiscreteQuotient.ofLE h t)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def stage : (DiscreteQuotient X)ᵒᵖ ⥤ CommRingCat.{0} where
  obj S := CommRingCat.of (S.unop → B)
  map f := CommRingCat.ofHom (preQ X B (leOfHom f.unop))
  map_id S := by
    refine CommRingCat.hom_ext (RingHom.ext fun g => funext fun t => ?_)
    exact congrArg g (DiscreteQuotient.ofLE_refl_apply t)
  map_comp f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun h => funext fun t => ?_)
    exact congrArg h (DiscreteQuotient.ofLE_ofLE _ _ t).symm

def pullQ (S : DiscreteQuotient X) : (S → B) →+* LocallyConstant X B where
  toFun g := ⟨fun x => g (S.proj x), S.proj_isLocallyConstant.comp g⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def lcCocone : Cocone (stage X B) where
  pt := CommRingCat.of (LocallyConstant X B)
  ι := { app := fun S => CommRingCat.ofHom (pullQ X B S.unop)
         naturality := fun S T f => by
           refine CommRingCat.hom_ext (RingHom.ext fun g => LocallyConstant.ext fun x => ?_)
           exact congrArg g (DiscreteQuotient.ofLE_proj _ x) }

def lcCoconeIsColimit : IsColimit (lcCocone X B) := by
  haveI : ReflectsColimitsOfShape (DiscreteQuotient X)ᵒᵖ (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget CommRingCat.{0})
  apply Types.FilteredColimit.isColimitOf
  · intro f
    refine ⟨op f.discreteQuotient, ⇑f.lift, ?_⟩
    exact LocallyConstant.ext fun x => rfl
  · intro S T g h e
    change pullQ X B S.unop g = pullQ X B T.unop h at e
    refine ⟨op (S.unop ⊓ T.unop), (homOfLE inf_le_left).op, (homOfLE inf_le_right).op, ?_⟩
    change preQ X B _ g = preQ X B _ h
    funext q
    obtain ⟨x, rfl⟩ := DiscreteQuotient.proj_surjective _ q
    have hx := congrArg (fun φ : LocallyConstant X B => φ x) e
    change g (S.unop.proj x) = h (T.unop.proj x) at hx
    exact (congrArg g (DiscreteQuotient.ofLE_proj _ x)).trans (hx.trans (congrArg h (DiscreteQuotient.ofLE_proj _ x).symm))

end GlobalTheory.EtC.LCSec

namespace GlobalTheory.EtC.LCSec

theorem res_res {R : Type} [CommRing R] {F : Shv R} {U V W : Scheme.{0}} (a : W ⟶ V) (b : V ⟶ U) (y : Sec F U) :
    Sec.res a (Sec.res b y) = Sec.res (a ≫ b) y := by
  simp [Sec.res]

theorem sec_pi_bijective (R : Type) [CommRing R] (F : Shv R) (B : Type) [CommRing B] (S : Type) [Finite S] :
    Function.Bijective (fun (y : Sec F (Spec (CommRingCat.of (S → B)))) (s : S) =>
      Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) s))) y) := by
  obtain ⟨hc⟩ := GlobalTheory.EtC.spec_pi_cofan_isColimit S (fun _ => B) (S → B) (RingEquiv.refl _)
  exact _root_.GlobalTheory.EtC.sec_coprod R F _ S _ _ hc

theorem res_eval_pullQ (R : Type) [CommRing R] (F : Shv R) (X : Type) [TopologicalSpace X] (B : Type) [CommRing B]
    (S : DiscreteQuotient X) (y : Sec F (Spec (CommRingCat.of (S → B)))) (x : X) :
    Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x)))
        (Sec.res (Spec.map (CommRingCat.ofHom (pullQ X B S))) y) =
      Sec.res (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : S => B) (S.proj x)))) y := by
  rw [res_res, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end GlobalTheory.EtC.LCSec

