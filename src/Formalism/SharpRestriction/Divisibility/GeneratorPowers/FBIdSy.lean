module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import Mathlib.AlgebraicGeometry.Modules.Sheaf

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)

section Alg

variable {S : Type} [CommRing S] (d : ℕ)

abbrev swJ (m : ℕ) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S)
      p.1 p.2

theorem mk_psTrunc_X {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (q : τ) :
    (Ideal.Quotient.mk (orig S τ ^ (m + 1)) (psTrunc m (MvPowerSeries.X q))) = Ideal.Quotient.mk _ (X q) := by
  rw [psTrunc_eq, ← MvPolynomial.coe_X, mk_trunc_coe]

end Alg

section Axes

variable {S : Type} [CommRing S] (d : ℕ)

abbrev axJ (m : ℕ) (b : Bool) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (if b then ![fun _ => 0, fun j => X ((0 : Fin 1), j)] else ![fun j => X ((0 : Fin 1), j), fun _ => 0] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2

def axV (b : Bool) (k : Fin 2) (j : Fin d) : MvPolynomial (Fin 1 × Fin d) S :=
  if (k = 1) = b then X ((0 : Fin 1), j) else 0

theorem axJ_X (m : ℕ) (b : Bool) (k : Fin 2) (j : Fin d) :
    axJ (S := S) d m b (Ideal.Quotient.mk _ (X (k, j))) = Ideal.Quotient.mk _ (axV d b k j) := by
  rw [axJ, jetSubstP, jetMap_mk, aeval_X]
  cases b <;> fin_cases k <;> simp [axV]

theorem psTrunc_zero {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) :
    psTrunc m (0 : MvPowerSeries τ S) = 0 := by
  simp [psTrunc]

theorem psJet_ev_ax (m : ℕ) (f : PS S 2 d) (b : Bool) :
    psJet m (ev (n := 1) (if b then ![0, pt S d 0] else ![pt S d 0, 0]) f) = axJ d m b (psJet m f) := by
  have ha : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((fun p : Fin 2 × Fin d => ((if b then ![0, pt S d 0] else ![pt S d 0, 0]) : Fin 2 → Pt S 1 d) p.1 p.2) p) = 0 := by
    rintro ⟨i, j⟩
    cases b <;> fin_cases i <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  rw [psJet_subst m _ ha f]
  refine DFunLike.congr_fun ?_ (psJet m f)
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨k, j⟩
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [axJ_X, jetMap_mk, aeval_X]
  cases b <;> fin_cases k <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, mk_psTrunc_X, axV, psTrunc_zero]

end Axes

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem scaleGenG_scaleGenG {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (v w : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    scaleGenG t φ ε v (scaleGenG t φ ε w g) = scaleGenG t φ ε (v * w) g := by
  simp only [scaleGenG, map_mul, mul_assoc]

theorem unitΓ_mul {A : Type} [CommRing A] (a b : Aˣ) : unitΓ (a * b) = unitΓ a * unitΓ b := by
  exact map_mul (Units.map (toΓ A).toMonoidHom) a b

theorem unitΓ_one {A : Type} [CommRing A] : unitΓ (1 : Aˣ) = 1 := by
  exact map_one (Units.map (toΓ A).toMonoidHom)

end Frame

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
