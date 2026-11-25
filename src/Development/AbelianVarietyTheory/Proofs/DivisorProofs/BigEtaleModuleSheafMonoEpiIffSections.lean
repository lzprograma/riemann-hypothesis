module

import Development.EtaleCohomology.TateTwists.EtaleSheafMonoEpiIffSectionsOfSeparation
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.EpiMono

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.MonoEpi

instance wEqLBMonoEpi (R : Type) [CommRing R] :
    (Scheme.etaleTopology.{0}).WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

variable {R : Type} [CommRing R]

theorem sec_ext {F G : Shv R} (φ ψ : F ⟶ G) (h : ∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) : φ = ψ := by
  apply Sheaf.hom_ext
  ext U a
  exact h (unop U) a

end GlobalTheory.EtC.MonoEpi

open GlobalTheory.EtC.MonoEpi in
theorem GlobalTheory.EtC.mono_epi_sections : ∀ (R : Type) [CommRing R] {F G : Shv R} (φ : F ⟶ G), (Mono φ ↔ ∀ U, Function.Injective (Sec.map φ (U := U))) ∧ (Mono φ ↔ ∀ U (a : Sec F U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0) ∧ (Epi φ ↔ ∀ U (b : Sec G U), Loc U fun V g => ∃ a : Sec F V, Sec.map φ a = Sec.res g b) ∧ (∀ ψ : F ⟶ G, (∀ U (a : Sec F U), Sec.map φ a = Sec.map ψ a) → φ = ψ) := by
  intro R _ F G φ
  exact ⟨LateralTheory.EtaleFoundations.MonoEpiPf.mono_iff_inj φ, (LateralTheory.EtaleFoundations.MonoEpiPf.mono_iff_inj φ).trans (LateralTheory.EtaleFoundations.MonoEpiPf.inj_iff_loc φ), LateralTheory.EtaleFoundations.MonoEpiPf.epi_iff φ, fun ψ h => sec_ext φ ψ h⟩
