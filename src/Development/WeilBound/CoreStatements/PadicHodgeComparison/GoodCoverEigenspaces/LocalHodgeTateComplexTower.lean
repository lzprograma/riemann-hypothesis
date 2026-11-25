module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IdTower
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.HTSpecAllHodge
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
public import Formalism.ConjugateSelfDual.Statement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalV GlobalTheory.HTLink GlobalTheory.HodgeCoh GlobalTheory.EtC GlobalTheory.Pst

namespace PositivityTheory.AutomorphicGaloisHodgeTate.G8

structure TowerBC {k k' : Type} [Field k] [Field k'] (φ : k →+* k') (H : HTower k) (H' : HTower k') {J : Type}
    (ι : J → H.Γ) (ι' : J → H'.Γ) where
  z : H'.Z ⟶ H.Z
  hz : IsPullback z H'.q H.q (spMap φ)
  y : ∀ j, H'.Y (ι' j) ⟶ H.Y (ι j)
  hs : ∀ j, IsPullback (y j) (H'.s (ι' j)) (H.s (ι j)) z
  ht : ∀ j, y j ≫ H.t (ι j) = H'.t (ι' j) ≫ z

variable {l : ℕ} [Fact l.Prime]

def HTCover {K : FinExt l} (H : HTower ↥K.1) {J : Type} (ι : J → H.Γ) (n : ℕ) : Prop :=
  ∃ (F : Frame (K := K) H.q n) (Φ : Matrix (Fin F.d) F.Col ℂ_[l]), F.IsHT Φ ∧
    ∀ j, ∃ (W : Scheme.{0}) (c : W ⟶ H.Z) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (I : Type) (_ : Fintype I)
      (σ : I → (W ⟶ H.Y (ι j))) (hσ : ∀ i, (σ i ≫ H.t (ι j)) ≫ H.q = c ≫ H.q), IsGalois c G a ∧ Splits (H.s (ι j)) c σ ∧
      ∃ (F' : Frame (K := K) (c ≫ H.q) n) (Φ' : Matrix (Fin F'.d) F'.Col ℂ_[l]),
        F.etMat F' rfl * Φ = Φ' * F.hodgeMat F' rfl ∧ ∀ i, F.etMat F' (hσ i) * Φ = Φ' * F.hodgeMat F' (hσ i)

def HTOcc {K : FinExt l} {d : ℕ} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (Qbar l)) (a : ℤ) : Prop :=
  ∃ (S : Finset (Qbar l)) (z : Fin d → ℂ_[l]), z ≠ 0 ∧ ∀ σ : ↥(GK K), (∀ x ∈ S, (σ : GQ l) x = x) →
    ((ρ σ).map (algebraMap (Qbar l) ℂ_[l])).mulVec (fun q => Formalism.Per.σC (σ : GQ l) (z q)) = chiPow (σ : GQ l) (-a) • z

end PositivityTheory.AutomorphicGaloisHodgeTate.G8

end
