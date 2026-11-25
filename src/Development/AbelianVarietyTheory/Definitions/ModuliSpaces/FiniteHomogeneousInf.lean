module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.ZM
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g : ℕ} {J : Type}

def SecCoord {X : Scheme.{0}} (M : LB X) {I : Type} (σ : I → M.Sec) {R : Type} [CommRing R] (x : Sp R ⟶ X) (v : I → R) : Prop :=
  ∃ τ : (M.pull x).Gen, τ.IsGen ∧ ∀ (i : I) (j : PUnit → M.ι) (h : (M.pull x).U j ≤ x ⁻¹ᵁ M.U (j PUnit.unit)),
    (x.appLE _ _ h).hom ((σ i).f (j PUnit.unit)) =
      resG (Sp R) le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) * (show Γ(Sp R, (M.pull x).U j) from (τ.s j).val)

structure MMPre (n N' : ℕ) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) where
  MM : Scheme.{0}
  s : MM ⟶ Sp o
  qproj : IsQProjOver s
  flat : Flat s
  reduced : IsReduced MM
  de : LB MM
  isLB : de.IsLB
  th : Ix g (N' ^ 2) → de.Sec
  loc : ∀ (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ MM) (v : Ix g (N' ^ 2) → R), x ≫ s = spMap β →
    SecCoord de th x v → InMM n N' I β v
  pts : ∀ (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R), InMM n N' I β v →
    ∃! x : Sp R ⟶ MM, x ≫ s = spMap β ∧ SecCoord de th x v

def TObj.Emb {N' : ℕ} {b : TBase o (N' ^ 2)} {s : S ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) (m : ℕ) (T : Over S)
    (σ : Ix g (N' ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) T)) : Prop :=
  ∃ (th : LB.Sec (Out.LPow t.A t.L 1 T)) (s1 : LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) T))
    (α : LB.Gen (LB.LinComb t.L (K := Fin 2) ![(snd T t.A).left, (snd T t.A ^ m).left] ![(m : ℤ) ^ 2, -1]))
    (U : Ix g (N' ^ 2) → Out.ThetaGrp t.A t.L ((m : ℤ) ^ 2) T),
    Out.IsGenSec t.A t.L 1 th ∧ α.IsGen ∧
    Out.IsTwistPull t.A t.L (Out.mulT t.A T m) (snd T t.A ^ m) (lift_snd _ _) ((m : ℤ) ^ 2) 1 α th s1 ∧
    (∀ a, Out.SymLift t.A t.L ((m : ℤ) ^ 2) (m ^ 2)
      (((Over.homMk T.hom (by simp) : T ⟶ Out.baseOver S) ≫ t.lab a) ^ ((N' / m) ^ 2)) (U a)) ∧
    ∀ a, Out.IsActOf t.A t.L ((m : ℤ) ^ 2) (U a) s1 (σ a)

def VeryDense {R : Type} [CommRing R] (P : Set (Ideal R)) : Prop :=
  ∀ (q : Ideal R) (f : R), q.IsPrime → f ∉ q → ∃ p ∈ P, p.IsPrime ∧ q ≤ p ∧ f ∉ p

def objPrimes {N' : ℕ} (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) {R : Type} [CommRing R]
    (β : o →+* R) (v : Ix g (N' ^ 2) → R) : Set (Ideal R) :=
  {p | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (t : TObj g (N' ^ 2) J b (spMap x ≫ spMap β)),
    RingHom.ker x = p ∧ t.Shape Mat κ ∧ t.HasTh (𝟙 _) (fun a => x (v a))}

def ProjRep {R σ : Type} [CommRing R] (I : Ideal (MvPolynomial σ R)) {Z : Scheme.{0}} (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) : Prop :=
  M.IsLB ∧ (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Z) (v : σ → R'), x ≫ s = spMap β → SecCoord M th x v →
    Ideal.span (Set.range v) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) ∧
  ∀ (R' : Type) [CommRing R'] (β : R →+* R') (v : σ → R'), Ideal.span (Set.range v) = ⊤ → (∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) →
    ∃! x : Sp R' ⟶ Z, x ≫ s = spMap β ∧ SecCoord M th x v

def idealOf {R σ : Type} [CommRing R] {Y X : Scheme.{0}} (s : Y ⟶ Sp R) (M : LB X) (th : σ → M.Sec) (a : Y ⟶ X) :
    Ideal (MvPolynomial σ R) :=
  ⨅ (R' : Type) (_ : CommRing R') (β : R →+* R') (y : Sp R' ⟶ Y) (v : σ → R') (_ : y ≫ s = spMap β ∧ SecCoord M th (y ≫ a) v),
    RingHom.ker (MvPolynomial.eval₂Hom β v)

def graphIdeal {R σ₁ σ₂ : Type} [CommRing R] {Y X₁ X₂ : Scheme.{0}} (s : Y ⟶ Sp R) (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁)
    (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂) : Ideal (MvPolynomial (σ₁ × σ₂) R) :=
  ⨅ (R' : Type) (_ : CommRing R') (β : R →+* R') (y : Sp R' ⟶ Y) (v₁ : σ₁ → R') (v₂ : σ₂ → R')
    (_ : y ≫ s = spMap β ∧ SecCoord M₁ th₁ (y ≫ a₁) v₁ ∧ SecCoord M₂ th₂ (y ≫ a₂) v₂),
    RingHom.ker (MvPolynomial.eval₂Hom β (fun i : σ₁ × σ₂ => v₁ i.1 * v₂ i.2))

def dimDeg {K σ : Type} [Field K] (I : Ideal (MvPolynomial σ K)) (e : ℕ) : ℕ :=
  Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e ⊓ I.restrictScalars K)

def vanIdeal {R σ Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R) : Ideal (MvPolynomial σ R) :=
  Ideal.span {F | F.IsHomogeneous d ∧ ∀ h, MvPolynomial.eval (p h) F = 0}

def CutBy {K σ Hh : Type} [Field K] (I : Ideal (MvPolynomial σ K)) (Q : Polynomial ℚ) (d : ℕ) (p : Hh → σ → K) : Prop :=
  ∀ e ≥ d, (dimDeg I e : ℚ) = Q.eval (e : ℚ) ∧ ∀ F, F.IsHomogeneous e → (F ∈ I ↔ F ∈ vanIdeal d p)

namespace OnePoint

def unitSec (X : Scheme.{0}) : (Out.Inh.trivLB X).Sec :=
  ⟨fun _ => 1, fun _ _ => (_root_.one_mul _).symm⟩

theorem restrict_restrict {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG X h' (resG X h a) = resG X (h'.trans h) a := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl


end OnePoint

end GlobalTheory.ZM
end
