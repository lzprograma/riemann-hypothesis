module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.TorsRatio

variable {V : Type} [CommRing V] [IsDomain V]

def cstK (z : (TFK (R := V) (FractionRing V)).left) :
    FractionRing V →+* (TFK (R := V) (FractionRing V)).left.presheaf.stalk z :=
  ((TFK (R := V) (FractionRing V)).left.presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom

theorem cst_eq_cstK (z : (TFK (R := V) (FractionRing V)).left) (a : FractionRing V) :
    GlobalTheory.UT.cst (R := V) (FractionRing V) z a = cstK z a :=
  gs_eq (𝟙 _) z ⊤ trivial _

theorem pt_eq (z z' : (TFK (R := V) (FractionRing V)).left) : z = z' :=
  Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) z z'

theorem cstK_surj (z : (TFK (R := V) (FractionRing V)).left) : Function.Surjective (cstK (V := V) z) := fun a => by
  obtain ⟨U, hU, s, rfl⟩ := (TFK (R := V) (FractionRing V)).left.presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => pt_eq z y ▸ hU
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv).2 s
  exact ⟨x, congrArg ((TFK (R := V) (FractionRing V)).left.presheaf.germ ⊤ z trivial).hom hx⟩

theorem frame_ratio {A : PolAV (Sp (FractionRing V))} {x : TFK (R := V) (FractionRing V) ⟶ A.A} {e e' : FrAt x}
    (he : e.IsGen) (he' : e'.IsGen) : ∃ l : FractionRing V, l ≠ 0 ∧ ∀ z J, Good A.L z J →
      (Geo.Tor.val e' (𝟙 _) z J).val = cstK z l * (Geo.Tor.val e (𝟙 _) z J).val := by
  let z : (TFK (R := V) (FractionRing V)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  choose J' hJ' using fun χ : (TFK (R := V) (FractionRing V)).left ⟶ A.A.left => Geo.Tor.exists_chart A.isLB (χ z)
  replace hJ' : Good A.L z J' := hJ'
  obtain ⟨l, hl⟩ := cstK_surj z (Geo.Tor.val e' (𝟙 _) z J' * (Geo.Tor.val e (𝟙 _) z J')⁻¹).val
  refine ⟨l, fun h => Units.ne_zero _ (hl.symm.trans (h ▸ map_zero _)), fun z' J hJ => ?_⟩
  obtain rfl := pt_eq z z'
  have t₁ : Geo.Tor.val e (𝟙 _) z J = _ * Geo.Tor.val e (𝟙 _) z J' :=
    gen_trans he (𝟙 _) z (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
  have t₂ : Geo.Tor.val e' (𝟙 _) z J = _ * Geo.Tor.val e' (𝟙 _) z J' :=
    gen_trans he' (𝟙 _) z (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
  rw [hl, t₁, t₂, ← Units.val_mul]
  exact congrArg Units.val (Additive.ofMul.injective (by simp only [ofMul_mul, ofMul_inv]; abel))

theorem valAt_torsFrame_ratio : ∀ (V : Type) [CommRing V] [IsDomain V] (A : PolAV (Sp (FractionRing V)))
    (ρA : LB.Gen (A.L.pull (eSec A.A))), ρA.IsGen → ∀ (N : ℕ), 1 ≤ N →
    ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e e' : FrAt x), IsTorsFrame A ρA N x e → IsTorsFrame A ρA N x e' →
    ∀ (th : SecA A (FractionRing V) 1) (c : FractionRing V), ValAt th x e c →
      ∃ u : FractionRing V, u ^ (N ^ 2) = 1 ∧ ValAt th x e' (u * c) := by
  intro V _ _ A ρA _ N _ x e e' H H' th c hv
  obtain ⟨-, he, α, hα, nα, cα⟩ := H
  obtain ⟨-, he', α', hα', nα', cα'⟩ := H'
  obtain ⟨l, hl0, hl⟩ := frame_ratio he he'
  have hαα := gen_unique A.isLB A.A.hom (eSec A.A) (Over.w η[A.A])
    (GlobalTheory.globalFns_holds _ _ A.isAb).2 hα hα' fun w I hI => by
      have a := val_corr hI nα (𝟙 _); have b := val_corr hI nα' (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b; exact a.trans b.symm
  let z : (TFK (R := V) (FractionRing V)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  choose J hJ using fun χ : (TFK (R := V) (FractionRing V)).left ⟶ A.A.left => Geo.Tor.exists_chart A.isLB (χ z)
  replace hJ : Good A.L z J := hJ
  have q : Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) = Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := by
    have a := val_corr hJ cα (𝟙 _); have b := val_corr hJ cα' (𝟙 _)
    have p₁ : Geo.Tor.val (powFrame A.A A.L x e ((N : ℤ) ^ 2)) (𝟙 _) z J = Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    have p₂ : Geo.Tor.val (powFrame A.A A.L x e' ((N : ℤ) ^ 2)) (𝟙 _) z J = Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    rw [val_mul hJ, val_pull hJ] at a b
    rw [← p₁, ← p₂, a, b, hαα _ _ z J hJ]
  have hlN : l ^ (N ^ 2) = 1 := (cstK z).injective <| by
    have q' := congrArg Units.val q
    rw [show ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
      Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hl z J hJ, mul_pow, ← map_pow] at q'
    rw [map_one]
    exact ((Units.isUnit _).pow _).mul_left_inj.1 (by rw [_root_.one_mul]; exact q'.symm)
  refine ⟨l⁻¹, by rw [inv_pow, hlN, inv_one], fun z' J' hJ' => ?_⟩
  rw [hv z' J' hJ']
  have r₁ : Geo.Tor.val (powFrame A.A A.L x e ((1 : ℕ) : ℤ)) (𝟙 _) z' J' = Geo.Tor.val e (𝟙 _) z' J' ^ ((1 : ℕ) : ℤ) := map_zpow _ _ _
  have r₂ : Geo.Tor.val (powFrame A.A A.L x e' ((1 : ℕ) : ℤ)) (𝟙 _) z' J' = Geo.Tor.val e' (𝟙 _) z' J' ^ ((1 : ℕ) : ℤ) := map_zpow _ _ _
  rw [r₁, r₂, Nat.cast_one, zpow_one, zpow_one, hl z' J' hJ']
  simp only [id, cst_eq_cstK]
  rw [← _root_.mul_assoc, ← map_mul, mul_comm l⁻¹ c, inv_mul_cancel_right₀ hl0]

end GlobalTheory.Poinc.TorsRatio
