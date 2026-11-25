module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Mathlib.RingTheory.OrderOfVanishing.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.Twist GlobalTheory.CechPic

namespace GlobalTheory.Vert

section Chi

variable {X Y : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)]

def chiLen (F : X.Modules) : ℤ := ∑ᶠ n, (-1 : ℤ) ^ n * (Module.length R (coh F n)).toNat

variable {F G : X.Modules}

theorem chiLen_eq_of_linearEquiv [Algebra R Γ(Y, ⊤)] {H : Y.Modules}
    (e : ∀ n, coh F n ≃ₗ[R] coh H n) : chiLen R F = chiLen R H :=
  finsum_congr fun n => by rw [(e n).length_eq]

theorem chiLen_congr (e : F ≅ G) : chiLen R F = chiLen R G :=
  chiLen_eq_of_linearEquiv R fun n => cohOn.mapIso R ⊤ n e

end Chi

section Twists

variable {X Y : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)]

def chiLenPic (F : X.Modules) : Pic X → ℤ :=
  Quotient.lift (fun M => chiLen R (twist F M.1)) fun M N h =>
    (Twist.nonempty_iso_of_lbIso M.2 N.2 h).elim (chiLen_congr R)

variable {F : X.Modules} {M : LB X}


variable (F) in
@[simp] theorem chiLenPic_cls (hM : M.IsLB) : chiLenPic R F (cls M hM) = chiLen R (twist F M) := rfl

end Twists

section Sym

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]


variable (G) in
abbrev SymQ : Type _ := SymmetricAlgebra ℚ (ℚ ⊗[ℤ] G)

def symOf : G →+ SymQ G :=
  (SymmetricAlgebra.ι ℚ _).toAddMonoidHom.comp (TensorProduct.mk ℤ ℚ G 1).toAddMonoidHom

theorem symOf_apply (g : G) : symOf g = SymmetricAlgebra.ι ℚ _ ((1 : ℚ) ⊗ₜ[ℤ] g) := rfl

def symLift {A : Type*} [CommRing A] [Algebra ℚ A] (f : G →+ A) : SymQ G →ₐ[ℚ] A :=
  SymmetricAlgebra.lift (LinearMap.liftBaseChange ℚ f.toIntLinearMap)

@[simp] theorem symLift_symOf {A : Type*} [CommRing A] [Algebra ℚ A] (f : G →+ A) (g : G) :
    symLift f (symOf g) = f g := by
  simp [symLift, symOf_apply]

def symMap (f : G →+ H) : SymQ G →ₐ[ℚ] SymQ H := symLift (symOf.comp f)

@[simp] theorem symMap_symOf (f : G →+ H) (g : G) : symMap f (symOf g) = symOf (f g) :=
  symLift_symOf _ g

end Sym

section SmallPic

variable {X Y Z : Scheme.{0}}

instance small_pic : Small.{0} (Pic X) := by
  refine small_of_surjective (α := {p : Σ U : X → X.Opens, ∀ i j, Γ(X, U i ⊓ U j)ˣ //
    LB.IsLB ⟨X, p.1, p.2⟩}) (f := fun p => cls _ p.2) fun c => ?_
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  choose j hj using LB.mem_of_cover hL
  have h : LB.IsLB ⟨X, fun x => L.U (j x), fun x y => L.g (j x) (j y)⟩ :=
    ⟨top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hj x⟩, fun _ => hL.g_self _,
      fun _ _ _ => hL.cocycle _ _ _⟩
  exact ⟨⟨⟨_, _⟩, h⟩, (cls_eq_iff h hL).2
    (iso_of_chart hL ⟨j, fun _ => le_rfl, fun _ _ _ _ _ => rfl⟩)⟩


variable (X) in
abbrev SmallPic : Type := Shrink.{0} (Pic X)


variable (X) in
def smallPicEquiv : SmallPic X ≃+ Pic X := Shrink.addEquiv

def smallCls (L : LB X) (hL : L.IsLB) : SmallPic X := (smallPicEquiv X).symm (cls L hL)

@[simp] theorem smallPicEquiv_smallCls (L : LB X) (hL : L.IsLB) :
    smallPicEquiv X (smallCls L hL) = cls L hL := (smallPicEquiv X).apply_symm_apply _

theorem smallCls_surj (c : SmallPic X) : ∃ L hL, smallCls L hL = c :=
  have ⟨L, hL, e⟩ := cls_surj (smallPicEquiv X c)
  ⟨L, hL, (smallPicEquiv X).symm_apply_eq.2 e⟩

theorem smallCls_eq_iff {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) :
    smallCls L hL = smallCls M hM ↔ LBIso L M :=
  (smallPicEquiv X).symm.injective.eq_iff.trans (cls_eq_iff hL hM)

def smallPull (f : Y ⟶ X) : SmallPic X →+ SmallPic Y :=
  (smallPicEquiv Y).symm.toAddMonoidHom.comp ((pull f).comp (smallPicEquiv X).toAddMonoidHom)


variable (X) in
abbrev PicSym : Type := SymQ (SmallPic X)

def c1 (L : LB X) (hL : L.IsLB) : PicSym X := symOf (smallCls L hL)

end SmallPic

end GlobalTheory.Vert
