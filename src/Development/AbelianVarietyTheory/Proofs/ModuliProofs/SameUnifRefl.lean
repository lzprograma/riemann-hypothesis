module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso

@[expose] public section

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def RigAlong {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (ε : G' ⟶ G) (L : RigLB G) (L' : RigLB G') (w : LB.Iso L'.L (L.L.pull ε.left)) : Prop :=
  w.IsGen ∧ PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig (𝟙 _)

variable {R : Type} [CommRing R] [IsDomain R]

def IsIdPull {D : DegPre R} (hD : IsPullDeg (RingHom.id R) D D) : Prop :=
  (∀ x, hD.xe x = x) ∧ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ ∧
    ∀ (Y : Scheme.{0}) (f : Y ⟶ D.P.A.left) (y : Y) (j k : D.P.L.ι), f y ∈ D.P.L.U j → f y ∈ D.P.L.U k →
      gw hD.w f y j k = gm f y _ (D.P.L.g j k)

theorem rigAlong_id {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) :
    RigAlong (𝟙 G) L L (isoPullId (idIso L.L) rfl) := by
  have he : eSec G ≫ (𝟙 G : G ⟶ G).left = 𝟙 _ ≫ eSec G := by simp
  exact ⟨(isGen_iff _).2 (isoPullId_pgen (idIso_isGen L.isLB) rfl),
    (maps_iff _ _ (fun _ => eSec G) _ L.rig L.rig (𝟙 _) _ (rigPull_le _ _ he L.L) (fun _ => rfl)).1
      (isoPullId_maps (idIso_maps L) rfl rfl he)⟩

end GlobalTheory.TorsionFormCompare
