module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.UU
namespace SecMod
variable {F : Type} [CommRing F] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of F)} {N : LB Y}

@[ext] theorem ext {s t : SecMod p N} (h : ∀ j, s.sec.f j = t.sec.f j) : s = t :=
  DVR.SecOps.sec_ext (s := s.sec) (t := t.sec) h

alias eq_zero_iff := _root_.GlobalTheory.UU.SecMod.eq_zero_iff_coord

section Val
variable {X Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
  {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (r : Z ⟶ Y)
include hJ

theorem sval_add (s t : SecMod p (LB.LinComb L φ ε)) :
    sval (s + t).sec r z J = sval s.sec r z J + sval t.sec r z J :=
  gs_add r z _ (hJ.mem φ r) _ _

alias sval_smul := _root_.GlobalTheory.UU.SecMod.value_smul

end Val


end SecMod
end GlobalTheory.UU
end
