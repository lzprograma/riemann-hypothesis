module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBase, Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBaseStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBase =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBase", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem texp_of_isSum {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    {a : D.toPre.P.A ⟶ D.toPre.P.A} {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G} {n j : ℤ} (τ : SecE U b n j)
    {Ix : Type} {w : Ix → D.toPre.X} (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β)
    (hs : Small I s) (hF : IsSum I s F) (hτ : TExp U τ s) : TExp U τ (w := id) F := by
  classical
  intro S hS Z x z J J' hJ hJ'
  have h0 : ∀ i ∉ (hs e).toFinset, Van I (s i) e := fun i hi => by
    by_contra h
    exact hi ((hs e).mem_toFinset.2 h)
  have hx : x ≫ (U.gt e).pG.left =
      (x ≫ (U.gt e).q.left) ≫ pullback.fst D.toPre.P.A.hom (thick R I e) := (Category.assoc _ _ _).symm
  rw [hτ _ h0 Z x z J J' hJ hJ']
  have hsum : ∀ δ, sval (F δ) (x ≫ (U.gt e).pG.left) z J =
      ∑ i ∈ (hs e).toFinset.filter (fun i => w i = δ), sval (s i) (x ≫ (U.gt e).pG.left) z J := fun δ => by
    rw [hx]
    convert hF e _ h0 δ Z (x ≫ (U.gt e).q.left) z J hJ
  have hvan : ∀ δ ∉ S, sval (F δ) (x ≫ (U.gt e).pG.left) z J = 0 := fun δ hδ => by
    rw [hx]
    exact hS δ hδ Z (x ≫ (U.gt e).q.left) z J hJ
  have key : ∀ T : Finset D.toPre.X, (hs e).toFinset.image w ⊆ T →
      ∑ i ∈ (hs e).toFinset, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val =
      ∑ δ ∈ T, sval (F δ) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t δ) x z J).val := fun T hT => by
    rw [← Finset.sum_fiberwise_of_maps_to (g := w) (t := T) (fun i hi => hT (Finset.mem_image_of_mem w hi))]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain rfl := (Finset.mem_filter.1 hi).2
    rfl
  rw [key _ (Finset.subset_union_left (s₂ := S))]
  refine (Finset.sum_subset Finset.subset_union_right fun δ _ hδ => ?_).symm
  exact (congrArg (· * _) (hvan δ hδ)).trans (zero_mul _)

theorem texp_sum : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j : ℤ) (τ : SecE U.toUnifPre b n j) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → TExp U.toUnifPre τ s → TExp U.toUnifPre τ (w := id) F :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U _ _ _ _ τ _ _ s F hs hF hτ => texp_of_isSum U.toUnifPre τ s F hs hF hτ

end GlobalTheory.TwFam
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBase =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBaseStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBaseStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBase\nimport Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBaseStatement =====
