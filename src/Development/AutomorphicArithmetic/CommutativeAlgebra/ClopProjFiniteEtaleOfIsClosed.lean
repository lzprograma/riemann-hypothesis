module

public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem UpperTheory.clopProj_finite_etale_of_isClosed :
    ∀ {S : Scheme.{0}} {T G : Over S} (V : (T ⊗ G).left.Opens), IsFinite G.hom → Etale G.hom → IsClosed (V : Set (T ⊗ G).left) → IsFinite (UpperTheory.RepresentationRank.proj V) ∧ Etale (UpperTheory.RepresentationRank.proj V) := by
  intro S T G V hf he hV
  have hpb : IsPullback (snd T G).left (fst T G).left G.hom T.hom :=
    (IsPullback.of_hasPullback T.hom G.hom).flip
  haveI : IsClosedImmersion V.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hV)
  haveI : IsFinite (fst T G).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) hpb hf
  haveI : Etale (fst T G).left :=
    MorphismProperty.of_isPullback (P := @Etale) hpb he
  exact ⟨inferInstanceAs (IsFinite (V.ι ≫ (fst T G).left)),
    inferInstanceAs (Etale (V.ι ≫ (fst T G).left))⟩
