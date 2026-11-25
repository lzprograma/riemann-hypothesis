module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsClassicalLevelDataCoverSelfDualStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsComponentsLatticesMovedToLevelFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionaryStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaAndMultipliers
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HarmonicRowHighestEqSpanIntegralHarmonicStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsStabiliserInvariantPullBoundedSectionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortSeriesReadingsEqClassicalThetaSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StableFormsEqSumThetaSeriesFreeLowerRowsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkingsStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierEqOneOnStabiliserStatement
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PolyDerivMonomialOne
import Std.Tactic.BVDecide.Normalize.Prop
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

namespace GlobalTheory.Dict

theorem isBddSec_of_mem_holSub {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (P : Formalism.L2.PjFree.FDSec X) (h : P ∈ Formalism.L2.PjFree.holSub X la) (k : Comp) (t : ℂ) :
    (X k).IsBddSec (la k) (t • P k) := by
  have h1 : ∀ k, P k ∈ (X k).SS (la k) := by
    induction h using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
    | add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
    | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)
  exact ((siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 t _ (h1 k)).1

theorem theta_sum_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} (X : Data E r)
    (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (φ : TF n g)
    {m : ℕ} (t : Fin m → ℂ) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (x : Frame X.Ψ r) :
    thP X hr bas idx φ (∑ i, t i • P i) x = ∑ i, t i * thP X hr bas idx φ (P i) x := by
  unfold thP
  rw [I2.jof_polyDeriv_sum]
  exact Finset.sum_congr rfl fun i _ => I2.polyDeriv_smul _ _ _ _ _



end GlobalTheory.Dict

namespace GlobalTheory.SupFull

theorem isBddSec_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {la : Wt X.Ψ r}
    {P : Frame X.Ψ r → ℂ} (t : ℂ) (h : X.IsBddSec la P) : X.IsBddSec la (t • P) := by
  obtain ⟨⟨h1, h2, h3⟩, C, hC⟩ := h
  refine ⟨⟨h1.const_smul t, fun x hx b hb => ?_, fun g hg x hx => ?_⟩, ‖t‖ * C, fun x hx => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, h2 x hx b hb]; ring
  · simp only [Pi.smul_apply, smul_eq_mul, h3 g hg x hx]; ring
  · rw [Formalism.L2.PjFree.pnorm_smul]
    exact mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg _)

end GlobalTheory.SupFull

namespace GlobalTheory.LargeCover

open GlobalTheory.Dict.Extend GlobalTheory.Dict.Pull

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def PrincUpTo (X : Data E r) (M : ℕ) (la : Wt X.Ψ r) : Prop :=
  ∀ ga : GL (Fin r) E, IsUStab X.Gm X.Λ ga →
    (∀ v ∈ X.Λ, ∃ u ∈ X.Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • u) →
      ∃ gb ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, bchar la b = 1 ∧ ∀ x, lact gb x = lact ga (rmul x b)

theorem conj_stab {X X' : Data E r} (hG : X'.Gm = X.Gm) {a g : GL (Fin r) E} {M : ℕ} (ha : IsUn X a) (hg : IsUn X g)
    (hfix : mapL g (mapL a X'.Λ) = mapL a X'.Λ)
    (hM : ∀ u ∈ mapL a X'.Λ, ∃ u' ∈ mapL a X'.Λ, (g : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u') :
    IsUStab X'.Gm X'.Λ (a⁻¹ * g * a) ∧
      ∀ v ∈ X'.Λ, ∃ u ∈ X'.Λ, ((a⁻¹ * g * a : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • u := by
  have hc : mapL (a⁻¹ * g * a) X'.Λ = X'.Λ := by
    rw [mapL_mul, mapL_mul, hfix, ← mapL_mul, inv_mul_cancel, mapL_one]
  refine ⟨⟨?_, fun x => ?_⟩, fun v hv => ?_⟩
  · rw [hG]
    exact isUn_mul (isUn_mul (isUn_inv ha) hg) ha
  · rw [← mem_mapL (a := a⁻¹ * g * a), hc]
  · obtain ⟨u', ⟨w, hw, e⟩, hu⟩ := hM _ (mem_mapL.2 hv)
    have e' : (a : Matrix (Fin r) (Fin r) E) *ᵥ w = u' := e
    refine ⟨w, hw, ?_⟩
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu, ← e',
      Matrix.mulVec_add, Matrix.mulVec_smul, inv_mulVec, inv_mulVec]

theorem princUpTo_of_hasPrinc {X : Data E r} {M : ℕ} (h : HasPrinc X M) (la : Wt X.Ψ r) :
    PrincUpTo X M la := by
  intro g hg hM
  let b : Frame X.Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)
  refine ⟨g, h g hg hM, b, fun τ => ⟨?_, fun i j hji => ?_⟩, ?_, fun x => ?_⟩
  · change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · change (1 : Matrix (Fin r) (Fin r) ℂ) i j = 0
    simp [hji.ne']
  · refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun i _ => ?_
    change ((1 : Matrix (Fin r) (Fin r) ℂ) i i) ^ _ = 1
    simp
  · have hb : rmul x b = x := by
      funext τ
      exact Matrix.mul_one _
    rw [hb]

end

theorem isStabForm_pull_upto (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X' X : Data E r) (h : SameSp X' X) (ga : GL (Fin r) E) (la' : Wt X'.Ψ r) (la : Wt X.Ψ r) (Δ : Subgroup (GL (Fin r) E)) (M : ℕ) (P : Frame X'.Ψ r → ℂ) (hga : IsUn X ga) (hl : ∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i) (hΔ : ∀ g' ∈ Δ, IsUn X g' ∧ (mapL g' (mapL ga X'.Λ) = mapL ga X'.Λ → ∀ u ∈ mapL ga X'.Λ, ∃ u' ∈ mapL ga X'.Λ, (g' : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')) (hP : PrincUpTo X' M la') (hχ : ChiOne X' la') (hb : X'.IsBddSec la' P) : IsStabForm X Δ (mapL ga X'.Λ) la (fun x => P (castFr h.psi.symm (lact ga⁻¹ x))) ∧ ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom ∧ castFr h.psi.symm (lact ga⁻¹ (lact ga (castFr h.psi x))) = x := by
  obtain ⟨⟨hd, hbor, hinv⟩, C, hC⟩ := hb
  have m1 : ∀ x ∈ X.dom, castFr h.psi.symm (lact ga⁻¹ x) ∈ X'.dom := fun x hx =>
    cast_GG h.psi.symm h.gm.symm h.p0.symm (lact_mem (isUn_inv hga) hx)
  have m2 : ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom := fun x hx =>
    lact_mem hga (cast_GG h.psi h.gm h.p0 hx)
  refine ⟨⟨?_, ?_, ?_, C, ?_⟩, fun x hx => ⟨m2 x hx, ?_⟩⟩
  · exact hd.comp ((cast_diff h.psi.symm).comp (differentiable_lact ga⁻¹)).differentiableOn m1
  · intro x hx b hb
    rw [lact_rmul, cast_rmul, hbor _ (m1 x hx) _ (cast_bor h.psi.symm hb), ← cast_bchar h.psi hl]
    rfl
  · intro g hg hfix x hx
    obtain ⟨s1, s2⟩ := conj_stab h.gm hga (hΔ g hg).1 hfix ((hΔ g hg).2 hfix)
    obtain ⟨gb, hgb, b, hb, hb1, hgbb⟩ := hP _ s1 s2
    have e : lact ga⁻¹ (lact g x) = lact (ga⁻¹ * g * ga) (lact ga⁻¹ x) := by
      rw [lact_lact, lact_lact, mul_inv_cancel_right]
    show P (castFr h.psi.symm (lact ga⁻¹ (lact g x))) = _
    have e2 := hinv _ hgb _ (m1 x hx)
    rw [hχ _ hgb, _root_.one_mul, hgbb, lact_rmul, hbor _ (lact_mem s1.1 (m1 x hx)) _ hb, hb1, _root_.one_mul] at e2
    rw [e, cast_lact, e2]
  · intro x hx
    refine le_of_eq_of_le ?_ (hC _ (m1 x hx))
    unfold Data.pnorm
    rw [cast_wt h.psi h.gm hl]
    simp only [dmin_lact (isUn_inv hga)]
  · rw [lact_lact, inv_mul_cancel, lact_one, cast_symm]

/-- Bounded sections vanishing off the frame domains lie in the span of the short theta
generators when the principal congruence action is trivial up to a weight-trivial Borel factor. -/
theorem bdd_mem_span_shortGen_upto
    (hci : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2)
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n)
    (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U)
    (hr1 : 1 ≤ r) (hA : l.A = 1)
    (hG : ∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0)
    (hlev : d.IsLev) (hnab : ∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂)
    (huc : UnitC d) (h3 : ¬ 3 ∣ d.pd) (hpin : Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀)
    (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (hbad : 0 < bad) (hdom : Dom a n)
    (hbig : 4 * (Module.finrank ℚ E * r) + 4 ≤ n)
    (hpr : ∀ k, PrincUpTo (U.X k) l.M (Formalism.L2.PjFree.laU U a n k))
    (hchi : ∀ k, ChiOne (U.X k) (Formalism.L2.PjFree.laU U a n k)) (htot : ShortValTot Xo c nab bad nV a n d)
    (P : Formalism.L2.PjFree.FDSec U.X) (hP1 : ∀ k, (U.X k).IsBddSec (Formalism.L2.PjFree.laU U a n k) (P k))
    (hP0 : ∀ k x, x ∉ (U.X k).dom → P k x = 0) :
    P ∈ Submodule.span ℂ (Formalism.L2.PjFree.rdU U '' shortGen Xo c nab bad nV a n d) := by
  rcases isEmpty_or_nonempty U.Comp with hemp | ⟨⟨k₀⟩⟩
  · have : P = 0 := funext fun k => (hemp.false k).elim
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨W⟩ := nonempty_uw hU
  have hrpq : r = Dw.p + Dw.q := hU.1
  have hn : r ≤ n := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    nlinarith
  have hev : Even n := by
    unfold Formalism.L2.Pj.Dom at hdom
    tauto
  have huw := GlobalTheory.T.uniformisation_component_lattices_markings E H Dw l Xo c σ r U hσ hU hr1 W
  have hsame : ∀ k, SameSp (U.X k) (U.X k₀) := fun k =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k₀).2 τ).symm, (hG k k₀).1,
      (hU.2.1 k).1.trans (hU.2.1 k₀).1.symm, (hG k k₀).2, by rw [(huw k).1, (huw k₀).1, (hG k k₀).2]⟩
  obtain ⟨ph, ψ, x₀, hph⟩ := hpin (hrpq ▸ hn)
  obtain ⟨Dc, hDe, -⟩ := GlobalTheory.T.exists_letterRowWeightDictionary E H Dw l c σ r W.g n (U.X k₀) a W.e hσ hrpq (hU.2.1 k₀).1 (hU.2.1 k₀).2
    (huw k₀).2.1 hdom
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_classicalLevelData_coverSelfDual E H Dw l Xo c n d σ r (U.X k₀) hn hrpq (huw k₀).2.1 hlev h3 ph ψ x₀ hph
  obtain ⟨v₀, mu, hv₀, hmu⟩ := GlobalTheory.SW.exists_vacua_and_multipliers E r (U.X k₀) W.g Dc.bas Dc.idx n Dc.sympl hev D
  obtain ⟨x0, ga, δ, hadm, hset, hsep⟩ := GlobalTheory.T.exists_components_lattices_moved_to_level_family E H Dw l Xo c n d σ r U hσ hU hr1 hA hlev W k₀ hsame ph D hn hD
  obtain ⟨u, hu, hread⟩ := GlobalTheory.T.short_series_readings_eq_classical_thetaSeries hci E H Dw l Xo c n d σ r U hσ hU hr1 hlev hnab huc ph ψ x₀ hph W (U.X k₀) a
    hdom Dc D hn hDe hD v₀ hv₀ x0
  choose C hC hrd using fun k => hread k (hsame k) (ga k) (δ k) (hset k).1 (hset k).2.1 (hset k).2.2.1
    (hset k).2.2.2.1 (hset k).2.2.2.2
  have hmu1 := _root_.GlobalTheory.Dict.mult_eq_one_on_stab E H Dw l Xo c n d σ r W.g (U.X k₀) Dc.bas Dc.idx D hn ph Dc.sympl hev hD
    (W.F.Di (W.ik k₀)) (W.emb k₀) (huw k₀).2.2.2.1 (huw k₀).2.2.2.2.1 (huw k₀).2.2.2.2.2.1 (huw k₀).2.2.2.2.2.2
    v₀ hv₀ mu hmu
  have hgrp := (GlobalTheory.SW.level_laws E r (U.X k₀) W.g Dc.bas Dc.idx n Dc.sympl hev D hn).2.2.1
  have hpull := fun k => isStabForm_pull_upto E r (U.X k) (U.X k₀) (hsame k) (ga k) (Formalism.L2.PjFree.laU U a n k)
    (wtOf (U.X k₀) Dc.hr Dc.k Dc.k' n) D.grp l.M ((C k)⁻¹ • P k) (hset k).1
    (fun τ i => by
      rw [Dc.wt_eq]
      simp only [wtX, Formalism.L2.PjFree.laU, (hsame k).p0])
    (fun g' hg' => ⟨((hgrp g').1 hg').1, fun hfix => (hmu1 _ (hset k).2.1 g' hg' hfix).2⟩)
    (hpr k) (hchi k) (GlobalTheory.SupFull.isBddSec_smul _ (hP1 k))
  have hM2 : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hMm : ((2 * bad * d.l₂.M : ℕ) : 𝓞 E) ∈ D.𝔪 := by
    rw [hD.m, Nat.cast_mul]
    refine Ideal.mul_mem_left _ _ ?_
    have h1 : (d.l₂.M : 𝓞 E) ∈ d.l₂.Mb * d.l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [d.l₂.prod]
      exact Ideal.mem_span_singleton_self _
    unfold Mfr
    exact (Submodule.mem_inf.1 (Ideal.mul_le_inf h1)).2
  obtain ⟨m, Λ, Pj, hΛ, hQ⟩ := _root_.GlobalTheory.Dict.stabForms_eq_sum_thP E r (U.X k₀) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hev hbig D hn
    (2 * bad * d.l₂.M) (Mfr l) (Jd d) (by positivity) hMm hD.prod hD.cop v₀ hv₀ mu hmu Dc.k Dc.k' U.Comp
    (fun k => mapL (ga k) (U.X k).Λ) _ (fun k => (hset k).2.1) hsep
    (fun k g' hg' hfix => (hmu1 _ (hset k).2.1 g' hg' hfix).1) (fun k => (hpull k).1)
  have hgl := fun j => GlobalTheory.Dict.GenLatCmp.genLat_vset E n (Λ j)
  have hg1 := fun j => (hgl j).1 bad d.l₂.M hbad d.l₂.odd (hΛ j).1
  choose N hN using fun j => (hg1 j).2.2.2
  have hV : ∀ j, Λ j ∈ Vset E n d.l₂.M := fun j => (hgl j).2.2.1 _ _ (Dvd.intro_left _ rfl) (hΛ j).1
  choose mj t R hR hPj using fun j => _root_.GlobalTheory.Dict.rowHighest_eq_sum_harmL E H Dw l c σ r W.g Dw.p n (U.X k₀) a Dc (Λ j) (N j)
    (hN j).1.pos ((hN j).2.2.trans inf_le_left) (Pj j) (hΛ j).2
  choose f hf hfr using fun j i => (htot ⟨Λ j⟩ (N j) x0 (R j i) (hg1 j).1 (hg1 j).2.1 (hg1 j).2.2.1 (hN j)
    (hadm _) (hR j i)).2
  have hPe : P = ∑ j, ∑ i, (t j i * (u (Λ j) (N j))⁻¹) • Formalism.L2.PjFree.rdU U (f j i) := by
    funext k x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ (U.X k).dom
    · obtain ⟨hx1, hx2⟩ := (hpull k).2 x hx
      have e1 := hQ k _ hx1
      rw [hx2, Pi.smul_apply, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ (hC k)] at e1
      rw [e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hPj j, theta_sum_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hrd k (Λ j) (hV j) (N j) (hN j) (R j i) (hR j i).1 (f j i) (hf j i) (hfr j i) x hx]
      have := hu (Λ j) (hV j) (N j) (hN j)
      field_simp
    · rw [hP0 k x hx]
      refine (Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_).symm
      have : Formalism.L2.PjFree.rdU U (f j i) k x = 0 := by
        simp [Formalism.L2.PjFree.rdU, hx]
      rw [this, mul_zero]
  rw [hPe]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨f j i, ⟨hf j i, ⟨Λ j⟩, N j, x0, R j i, (hg1 j).1, (hg1 j).2.1, (hg1 j).2.2.1, hN j,
    hadm _, hR j i, hfr j i⟩, rfl⟩

end GlobalTheory.LargeCover

namespace GlobalTheory.Dict

theorem holSub0_le_span_shortGen : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → l.A = 1 → (∀ k k', (U.X k).Gm = (U.X k').Gm ∧ (U.X k).ξ0 = (U.X k').ξ0) → (∀ k, HasPrinc (U.X k) l.M) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → ¬ 3 ∣ d.pd → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < bad → Dom a n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → (∀ k, ChiOne (U.X k) (Formalism.L2.PjFree.laU U a n k)) → ShortValTot Xo c nab bad nV a n d → holSub0 U.X (Formalism.L2.PjFree.laU U a n) ≤ Submodule.span ℂ (Formalism.L2.PjFree.rdU U '' shortGen Xo c nab bad nV a n d) := by
  intro hci E _ _ _ H Dw l Xo c n d σ r U hσ hU hr1 hA hG hpr hlev hnab huc h3 hpin nab bad nV a hbad hdom hbig
    hchi htot P hP
  refine GlobalTheory.LargeCover.bdd_mem_span_shortGen_upto hci E H Dw l Xo c n d σ r U hσ hU hr1 hA hG hlev hnab huc h3 hpin
    nab bad nV a hbad hdom hbig (fun k => GlobalTheory.LargeCover.princUpTo_of_hasPrinc (hpr k) _) hchi htot P ?_ hP.2
  intro k
  simpa only [one_smul] using isBddSec_of_mem_holSub U.X _ P hP.1 k 1

end GlobalTheory.Dict
