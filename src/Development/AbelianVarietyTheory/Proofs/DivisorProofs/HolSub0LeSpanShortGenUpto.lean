module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsClassicalLevelDataCoverSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsComponentsLatticesMovedToLevelFamilyStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFormExtendToAllLattices
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionaryStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaAndMultipliers
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HarmonicRowHighestEqSpanIntegralHarmonicStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsStabiliserInvariantPullBoundedSection
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortSeriesReadingsEqClassicalThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StableFormsEqSumThetaSeriesFreeLowerRowsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkingsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierEqOneOnStabiliserStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
open GlobalTheory.Dict

open GlobalTheory.Dict.Extend GlobalTheory.Dict.Pull

namespace GlobalTheory.LargeCover

section Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_pow_root_eq_one (K : Type) [Field K] [NumberField K] :
    ∃ w : ℕ, 0 < w ∧ ∀ (u : K) (n : ℕ), 0 < n → u ^ n = 1 → u ^ w = 1 := by
  refine ⟨NumberField.Units.torsionOrder K, NumberField.Units.torsionOrder_pos K, fun u n hn hu => ?_⟩
  have hi : IsIntegral ℤ u := IsIntegral.of_pow hn (hu ▸ isIntegral_one)
  have h1 : (⟨u, hi⟩ : 𝓞 K) ^ n = 1 := Subtype.ext hu
  let v : (𝓞 K)ˣ := Units.ofPowEqOne _ n h1 hn.ne'
  have hv : v ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, Units.pow_ofPowEqOne h1 hn.ne'⟩)
  have h2 : (⟨v, hv⟩ : NumberField.Units.torsion K) ^ NumberField.Units.torsionOrder K = 1 := by
    unfold NumberField.Units.torsionOrder
    first | exact pow_card_eq_one'
  have h3 : v ^ NumberField.Units.torsionOrder K = 1 := congrArg Subtype.val h2
  exact congrArg (fun x : (𝓞 K)ˣ => ((x : 𝓞 K) : K)) h3

theorem princUpTo_of_root (X : Data E r) (M w : ℕ) (hw : ∀ (u : E) (n : ℕ), 0 < n → u ^ n = 1 → u ^ w = 1)
    (la : Wt X.Ψ r) (hla : ∀ τ i, (w : ℤ) ∣ la τ i)
    (h : ∀ ga : GL (Fin r) E, IsUStab X.Gm X.Λ ga →
      (∀ x ∈ X.Λ, ∃ y ∈ X.Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ x - x = (M : E) • y) →
      ∃ gb ∈ X.Γ, ∃ (u : E) (n : ℕ), 0 < n ∧ u ^ n = 1 ∧
        (gb : Matrix (Fin r) (Fin r) E) = u • (ga : Matrix (Fin r) (Fin r) E)) : PrincUpTo X M la := by
  intro ga hga hc
  obtain ⟨gb, hgb, u, n, hn, hu, he⟩ := h ga hga fun x hx => by
    obtain ⟨y, hy, e⟩ := hc x hx
    exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
  have hu0 : u ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hu; exact zero_ne_one hu
  let b : Frame X.Ψ r := fun τ => (Matrix.diagonal fun _ => τ.1 u : Matrix (Fin r) (Fin r) ℂ)
  have hb : ∀ τ, mat b τ = τ.1 u • (1 : Matrix (Fin r) (Fin r) ℂ) := fun τ => by
    rw [Matrix.smul_one_eq_diagonal]; rfl
  refine ⟨gb, hgb, b, fun τ => ⟨?_, fun a c hac => Matrix.diagonal_apply_ne _ hac.ne'⟩, ?_, fun x => ?_⟩
  · rw [hb, Matrix.det_smul, Matrix.det_one, _root_.mul_one]
    exact pow_ne_zero _ ((map_ne_zero τ.1).2 hu0)
  · refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun i _ => ?_
    obtain ⟨k, hk⟩ := hla τ i
    have : b τ i i = τ.1 u := Matrix.diagonal_apply_eq _ i
    rw [this, hk, _root_.zpow_mul, zpow_natCast, ← map_pow, hw u n hn hu, map_one, _root_.one_zpow]
  · funext τ
    show (gb : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
      (ga : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ)
    have : (u • (ga : Matrix (Fin r) (Fin r) E)).map τ.1 = τ.1 u • (ga : Matrix (Fin r) (Fin r) E).map τ.1 := by
      ext a c; simp
    rw [he, this, hb, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]

end Pull



theorem holSub0_le_span_shortGen_upto : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ¬ 3 ∣ d.pd → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, PrincUpTo (U.X k) l.M (Formalism.L2.PjFree.laU U a n k)) → (∀ k, ChiOne (U.X k) (Formalism.L2.PjFree.laU U a n k)) → ShortValTot Xo c nab bad nV a n d → holSub0 U.X (Formalism.L2.PjFree.laU U a n) ≤ Submodule.span ℂ (Formalism.L2.PjFree.rdU U '' shortGen Xo c nab bad nV a n d) := by
  intro hci E _ _ _ H Dw l Xo c n d σ r U hσ hU hr1 hA hG hlev hnab huc h3 hpin nab bad nV a hbad hdom hbig
    hpr hchi htot P hP
  refine GlobalTheory.LargeCover.bdd_mem_span_shortGen_upto hci E H Dw l Xo c n d σ r U hσ hU hr1 hA hG hlev hnab huc h3 hpin
    nab bad nV a hbad hdom hbig hpr hchi htot P ?_ hP.2
  intro k
  simpa only [one_smul] using isBddSec_of_mem_holSub U.X _ P hP.1 k 1

end GlobalTheory.LargeCover
