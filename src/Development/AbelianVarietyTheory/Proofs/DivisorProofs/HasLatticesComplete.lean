module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.TwoSeq GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.BadPt

section Linear

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {H : Type*} [AddCommGroup H] [Module K H] [Module R H]
  [IsScalarTower R K H]

end Linear

section Sheaf

variable {O : Type} [CommRing O] {X T : Scheme.{0}} {R K : Type} [CommRing R] [Field K] [Algebra R K]
  {f : Sp R ⟶ X} {f₀ : T ⟶ X} {ξ : Sp K ⟶ T}

def resSec (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) (A : X.Modules) (t : Γ((Scheme.Modules.pullback f).obj A, ⊤)) :
    Γ((Scheme.Modules.pullback ξ).obj ((Scheme.Modules.pullback f₀).obj A), ⊤) :=
  ((sqIso w).hom.app A).app ⊤ (QCoh.pullbackSections (spMap (algebraMap R K)) _ (V := ⊤) le_top t)


variable (w : spMap (algebraMap R K) ≫ f = ξ ≫ f₀) {A B A' B' : X.Modules} {D : T.Modules}
  (a : (Scheme.Modules.pullback f₀).obj A ⟶ D) (b : D ⟶ (Scheme.Modules.pullback f₀).obj B)

def Reads {H : Type*} [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H]
    (E : Γ((Scheme.Modules.pullback ξ).obj D, ⊤) ≃+ H) (β : LinearMap.BilinForm K H) (F : Submodule K H)
    (N : Submodule R H) : Prop :=
  (∀ s, ((Scheme.Modules.pullback ξ).map b).app ⊤ s = 0 ↔ E s ∈ F) ∧
    (∀ s, E s ∈ N ↔ ∃ t, s = ((Scheme.Modules.pullback ξ).map a).app ⊤ (resSec w A t)) ∧
    (∀ s, E s ∈ β.dualSubmodule N ↔ ∃ t, ((Scheme.Modules.pullback ξ).map b).app ⊤ s = resSec w B t) ∧
    Function.Surjective (((Scheme.Modules.pullback ξ).map b).app ⊤)


variable {α : O →+* End A} {β : O →+* End B} {α' : O →+* End A'} {β' : O →+* End B'} {r : ℕ}

end Sheaf

section Forms

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

end Forms

section Tower

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K]

structure FinTower (Γ : PDivGroup p R) (G : Over (Sp R)) [GrpObj G] : Type where

  y : ∀ n, SpAlg R (Γ.A n) ⟶ G

  mul : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] (φ ψ : WithConv (Γ.A n →ₐ[R] B)),
    spOver (φ * ψ).ofConv ≫ y n = (spOver φ.ofConv ≫ y n) * (spOver ψ.ofConv ≫ y n)

  inj : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] (φ ψ : Γ.A n →ₐ[R] B),
    spOver φ ≫ y n = spOver ψ ≫ y n → φ = ψ

  surj : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] (z : SpAlg R B ⟶ G),
    z ^ p ^ n = 1 → ∃ φ : Γ.A n →ₐ[R] B, spOver φ ≫ y n = z

  res : ∀ n, spOver (Γ.res n : Γ.A (n + 1) →ₐ[R] Γ.A n) ≫ y (n + 1) = y n

def IsWeilHom {𝒜 ℬ : PDivGroup p R} {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (t : 𝒜.TorsionTower A)
    (u : ℬ.TorsionTower B) (P : LB (A ⊗ B).left) (w : 𝒜 ⟶ ℬ.dual) : Prop :=
  ∀ n, ∃ U : (𝒜.A n ⊗[R] ℬ.A n)ˣ,
    Out.WeilIs (A ⊗ B) P ((p ^ n : ℕ) : ℤ) (T := SpAlg R (𝒜.A n ⊗[R] ℬ.A n))
      (CartesianMonoidalCategory.lift
        (spOver (Algebra.TensorProduct.includeLeft : 𝒜.A n →ₐ[R] 𝒜.A n ⊗[R] ℬ.A n) ≫ t.y n) 1)
      (CartesianMonoidalCategory.lift 1
        (spOver (Algebra.TensorProduct.includeRight : ℬ.A n →ₐ[R] 𝒜.A n ⊗[R] ℬ.A n) ≫ u.y n))
      (unitOn U) ∧
    ∀ χ : CartierDual R (ℬ.A n), w.app n χ = TensorProduct.rid R _ (χ.ofConv.lTensor _ U.val)

variable [Fact p.Prime] {Γ : PDivGroup p R} {𝒜 : PDivGroup p K}

variable [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt]

end Tower

end GlobalTheory.BadPt
