module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne

@[expose] public section

noncomputable section

open CategoryTheory GlobalTheory.CatCoh

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

def CovBy {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (Φ : C → Prop) (S : C) : Prop :=
  ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧
    ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → Φ S'

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
