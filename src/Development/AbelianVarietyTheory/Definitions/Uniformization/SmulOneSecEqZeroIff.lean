module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Tactic.Linter.Style

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
noncomputable section
namespace GlobalTheory.UU

def SecMod {F : Type} [CommRing F] {Y : Scheme.{0}} (_p : Y ⟶ Spec (CommRingCat.of F)) (N : LB Y) : Type := LB.Sec N
namespace SecMod
variable {F : Type} [CommRing F] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of F)} {N : LB Y}

def sec (s : SecMod p N) : LB.Sec N := s

def mk (p : Y ⟶ Spec (CommRingCat.of F)) (s : LB.Sec N) : SecMod p N := s

instance : Zero (SecMod p N) := ⟨DVR.SecOps.secZero⟩

instance : Add (SecMod p N) := ⟨DVR.SecOps.secAdd⟩

instance : Neg (SecMod p N) := ⟨DVR.SecOps.secNeg⟩

instance : SMul F (SecMod p N) := ⟨fun c s => DVR.SecOps.secScale (scal p c) s⟩

instance : AddCommGroup (SecMod p N) where
  add_assoc _ _ _ := DVR.SecOps.sec_ext fun _ => add_assoc _ _ _
  zero_add _ := DVR.SecOps.sec_ext fun _ => zero_add _
  add_zero _ := DVR.SecOps.sec_ext fun _ => add_zero _
  neg_add_cancel _ := DVR.SecOps.sec_ext fun _ => neg_add_cancel _
  add_comm _ _ := DVR.SecOps.sec_ext fun _ => add_comm _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module F (SecMod p N) where
  one_smul s := DVR.SecOps.sec_ext fun i => by
    show resTop _ (scal p 1) * s.f i = s.f i
    simp [scal]
  mul_smul a b s := DVR.SecOps.sec_ext fun i => by
    show resTop _ (scal p (a * b)) * s.f i = resTop _ (scal p a) * (resTop _ (scal p b) * s.f i)
    simp [scal, _root_.mul_assoc]
  smul_zero _ := DVR.SecOps.sec_ext fun _ => mul_zero _
  smul_add _ _ _ := DVR.SecOps.sec_ext fun _ => mul_add _ _ _
  add_smul a b s := DVR.SecOps.sec_ext fun i => by
    show resTop _ (scal p (a + b)) * s.f i = resTop _ (scal p a) * s.f i + resTop _ (scal p b) * s.f i
    simp [scal, add_mul]
  zero_smul s := DVR.SecOps.sec_ext fun i => by
    show resTop _ (scal p 0) * s.f i = 0
    simp [scal]

@[simp] theorem coord_zero (j : N.ι) : (0 : SecMod p N).sec.f j = 0 := rfl

@[simp] theorem coord_smul (c : F) (s : SecMod p N) (j : N.ι) :
    (c • s).sec.f j = resTop (N.U j) (scal p c) * s.sec.f j := rfl

@[simp] theorem coord_mk (s : LB.Sec N) (j : N.ι) : (mk p s).sec.f j = s.f j := rfl


theorem eq_zero_iff_coord (s : SecMod p N) : s = 0 ↔ ∀ j, s.sec.f j = 0 := by
  constructor
  · rintro rfl j
    exact coord_zero j
  · intro h
    exact DVR.SecOps.sec_ext fun j => (h j).trans (coord_zero j).symm

section Val
variable {X Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
  {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (r : Z ⟶ Y)
include hJ

theorem value_smul (c : F) (s : SecMod p (LB.LinComb L φ ε)) :
    sval (c • s).sec r z J = gs r z ⊤ (scal p c) * sval s.sec r z J := by
  refine (congrArg (gs r z (LB.wchart L φ fun k => J (r ≫ φ k))) (coord_smul c s _)).trans ?_
  exact (gs_mul r z _ (hJ.mem φ r) _ _).trans
    (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) _))

end Val

end SecMod
end GlobalTheory.UU
end
