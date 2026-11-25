module

public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

section Fam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

def letE (Dw : Datum H) : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
  (Fintype.equivFin _).symm

def tyOf (c : Coeff l) (σ : c.F →+* ℂ) (Dw : Datum H) : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) → (E →+* ℂ) :=
  fun i => relab c σ (letE Dw i).1

def RelabType (c : Coeff l) (σ : c.F →+* ℂ) (Dw : Datum H) : Prop := IsTypeFn H Dw.p Dw.q (tyOf c σ Dw)

variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def famOf (hN : N1c) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (hpq : 1 ≤ Dw.p + Dw.q) (hσ : GoodEmb c σ)
    (hR : RelabType c σ Dw) :
    FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (letE Dw j).1) :=
  Classical.choice (hN E H Dw l Xo _ _ _ hpq hσ hR)

structure ModelsOf {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} (F : FamilyUnif Xo σ' ty) (r : ℕ) : Type 1 where
  X : Fin F.n → Data E r
  φ : ∀ i, (F.Di i).La ≃ₗ[𝓞 E] (X i).Λ

structure ModelBase {g : ℕ} {ty : Fin g → (E →+* ℂ)} {σ' : KA l →+* ℂ} {F : FamilyUnif Xo σ' ty} (M : ModelsOf F r) :
    Prop where
  rank : r = Dw.p + Dw.q
  type : ∀ k, (M.X k).p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ (M.X k).Ψ ↔ τ (H.rt : E) = H.rt0
  chi : ∀ k la γ, (M.X k).χ la γ = 1
  ef : ∀ k a b, (((F.Di k).EF a b : ℤ) : ℚ) =
    Algebra.trace ℚ E (-(M.X k).ξ0 * herm (M.X k).Gm (M.φ k a : Fin r → E) (M.φ k b))
  gam : ∀ k (γ : GL (Fin r) E), γ ∈ (M.X k).Γ ↔ IsUStab (M.X k).Gm (M.X k).Λ γ ∧
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ b : (F.Di k).La,
      (γ : Matrix (Fin r) (Fin r) E).mulVec (M.φ k a : Fin r → E) =
        (M.φ k a : Fin r → E) + (l.M : ℕ) • (M.φ k b : Fin r → E)) ∧
    ∀ a : (F.Di k).La, ∃ b : (F.Di k).La,
      (γ : Matrix (Fin r) (Fin r) E).mulVec (M.φ k a : Fin r → E) = (M.φ k a : Fin r → E) + (l.A : ℕ) • (M.φ k b : Fin r → E)
  domStab : ∀ k, ∀ x ∈ (M.X k).dom, (∀ b ∈ Bor (M.X k).Ψ r, rmul x b ∈ (M.X k).dom) ∧
    ∀ γ ∈ (M.X k).Γ, lact γ x ∈ (M.X k).dom

theorem rdU_mem (U : Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) {x : Frame (U.X k).Ψ r} (h : x ∈ (U.X k).dom) :
    rdU U f k x = toC (evR Xo c f (U.un k ⟨x, h⟩)) := by
  simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dite_eq_left h]

instance (σ : c.F →+* ℂ) : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)

end Fam

section Dict2

variable {Comp : Type}

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}


open Classical in
def DictSpec (U : Unf Xo c σ r) (V : HSp D) (hr : V.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) {g : ℕ} (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (h : GA D V) (p : Σ k, Frame (U.X k).Ψ r) : Prop :=
  ∃ γ ∈ GQ V,
      ((U.X p.1).Λ : Set (Fin r → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
        ∃ w ∈ latGHat V (γ * h),
        finVec V ((φ p.1 (F.t (ik p.1) a) : Fin r → D.host.E) ∘ Fin.cast hr) -
          (finHom V (γ * h)).1.mulVec (finVec V (ι a)) = (l.M : ℕ) • w) ∧
      ∀ τ : (U.X p.1).Ψ, mat p.2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th p.1 τ) (γ * h)) * x₀ τ.1



def DetRootMul (V : HSp D) : Prop :=
  ∀ g g' x x', IsDetRoot V g x → IsDetRoot V g' x' → IsDetRoot V (g * g') (x * x')

theorem detRootMul_holds (V : HSp D) : DetRootMul V := by
  intro g g' x x' hx hx'
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

end Dict2

section Rows

variable {D : D7}

def XiConst (D : D7) : Prop := ∀ τ : D.host.E →+* ℂ, ‖τ D.host.xi0‖ = xiR D

theorem xiConst_holds (D : D7) : XiConst D := by
  intro τ
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, sq_emb, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

end Rows

end Formalism.L2.Pj
