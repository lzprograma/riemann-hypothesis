module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicMatrixMemLatticeOfColumnsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenMapTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSumConjSumOrthogonalDvdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubIdempotentSmulMemLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
open GlobalTheory.SingleDatum




namespace GlobalTheory.AdTh.MovedSum

open GlobalTheory.AdTh.MovedDatum

section Lemmas

open MeasureTheory
open scoped ComplexConjugate

variable {D : D7}

theorem finite_levQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hM : l.Mb ≠ ⊥ := by
    intro h
    have h₁ := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := l.Mb.finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem exists_pow_mem_Mb {H : Geo.Tor.Host D.host.E} (l : Geo.Tor.Level H) (s : 𝓞 D.host.E)
    (hs : ∀ PP : Formalism.L2.DIV.Pl D.host.E, l.Mb ≤ PP.asIdeal → s ∈ PP.asIdeal) : ∃ j : ℕ, s ^ j ∈ l.Mb := by
  have hbot : l.Mb ≠ ⊥ := by
    intro h
    have h₁ := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have : s ∈ l.Mb.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    have hJ0 : J ≠ ⊥ := fun h0 => hbot (le_bot_iff.1 (h0 ▸ hJ))
    exact hs ⟨J, hJp, hJ0⟩ hJ
  exact this

theorem pow_sep {H : Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Geo.Tor.Level H) (s : 𝓞 D.host.E) (j : ℕ)
    (hj : s ^ j ∈ l.Mb) (v : Dw.La) : ∃ z : Dw.La, s ^ j • (cSep l • v) = l.M • z := by
  have hex : ∃ c, c ∈ Mfr l ∧ c - 1 ∈ l.Mb := by
    have : (1 : 𝓞 D.host.E) ∈ l.Mb ⊔ Mfr l := by rw [show l.Mb ⊔ Mfr l = ⊤ from l.coprime]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 this
    exact ⟨y, hy, by rw [← hxy, sub_add_cancel_right]; exact neg_mem hx⟩
  have hc : cSep l ∈ Mfr l := by
    unfold cSep; rw [dite_eq_left hex]; exact hex.choose_spec.1
  have hm : s ^ j * cSep l ∈ Ideal.span {(l.M : 𝓞 D.host.E)} := by
    rw [← l.prod]; exact Ideal.mul_mem_mul hj hc
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hm
  refine ⟨t • v, ?_⟩
  rw [smul_smul, ← ht, ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E) l.M (t • v), smul_smul, mul_comm]

theorem one_sub_smul_mem_latO_pow (V W : HSp D) (LV : Set (Fin V.rank → D.host.E)) (LW : Set (Fin W.rank → D.host.E))
    (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (he : IsIdemSum e P) (x : WO V W)
    (hx : ∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∈ PP.asIdeal) →
      ∃ j : ℕ, incA D ((s ^ j : 𝓞 D.host.E) : D.host.E) • x ∈ (latO V W LV LW fun _ => True)) :
    (1 - e) • x ∈ (latO V W LV LW fun _ => True) := by
  obtain ⟨y, hy0, hy, hw⟩ := GlobalTheory.OffIdem.exists_den he
  obtain ⟨j, hj⟩ := hx y hy
  rw [show ((y ^ j : 𝓞 D.host.E) : D.host.E) = (y : D.host.E) ^ j from map_pow (algebraMap (𝓞 D.host.E) D.host.E) y j] at hj
  have h1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have h2 : (1 - e) * (1 - e) = 1 - e := GlobalTheory.OffIdem.one_sub_mul_self (R := AE D) h1
  have hi : finPart D (1 - e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, h2])
  set f : AE D := (1 - e) * incA D ((y : D.host.E)⁻¹) with hf
  have hpow : ∀ n : ℕ, ∀ z ∈ (latO V W LV LW fun _ => True), f ^ n • z ∈ (latO V W LV LW fun _ => True) := by
    intro n
    induction n with
    | zero => intro z hz; rwa [pow_zero, one_smul]
    | succ n ih =>
      intro z hz
      rw [pow_succ', mul_smul]
      exact GlobalTheory.LatticeStable.smul_mem_latO D V W LV LW _ _ hw _ (ih z hz)
  have hp : ∀ n : ℕ, (1 - e) * (1 - e) ^ n = 1 - e := by
    intro n
    induction n with
    | zero => rw [pow_zero, mul_one]
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, h2]
  have hyy : incA D ((y : D.host.E)⁻¹) * incA D (y : D.host.E) = 1 := by
    rw [← RingHom.map_mul, inv_mul_cancel₀ hy0, RingHom.map_one]
  have key : (1 - e) * (f ^ j * incA D ((y : D.host.E) ^ j)) = 1 - e := by
    rw [map_pow, ← mul_pow, hf, mul_assoc, hyy, mul_one, hp]
  have := GlobalTheory.LatticeStable.smul_mem_latO D V W LV LW _ _ hi _ (hpow j _ hj)
  rwa [smul_smul, smul_smul, mul_assoc, key] at this

theorem step_pow (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (V W : HSp D) (hV : V.gram = 1) {r : ℕ}
    (hr : W.rank = r) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (a1 : (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V)
    (a2 : (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W) (a3 : IsSelfDualC V ΛV) (a4 : IsSelfDualC W ΛW)
    (a5 : (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)))
    {H : Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Geo.Tor.Level H)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (hι : LatEmb W ι) (δ : ℤ)
    (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, l.Mb ≤ PP.asIdeal ∧ (2 : 𝓞 D.host.E) ∉ PP.asIdeal) (bad N : ℕ) (h : GA D V) (k : GA D W)
    (Λ : GenLat D.host.E V.rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (hbad : ∀ PP ∈ P, ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (hh : SplitOffBad V bad h)
    (hΛ : ∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (fin V h)) (hT : Λ.TrivAt l.M) (hL : Λ.LevOK N l.M)
    (hmk : MarkAd l W hr ι k mk) (Y : (Fin V.rank → LevQ Dw l) → Matrix (Fin V.rank) (Fin r) D.host.E)
    (hY : IsRoots l (latR hr (latG W k)) mk N Y) (q : Fin V.rank → LevQ Dw l)
    (hq : ∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∈ PP.asIdeal) → ∃ j : ℕ, ∀ b, ∃ z : Dw.La, s ^ j • (cSep l • levRep (q b)) = l.M • z)
    (γ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : WO V W) (hγ : colsR hr γ = δ • Y q) (hu : IsFinOf V W γ u) :
    ∃ c₀ ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True,
      u = actO V W h k (Matrix.of fun a b => e * incA D ((δ : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))) +
        2 • actO V W h k c₀ ∧
      ψ (symplOH V W (actO V W h k
        (Matrix.of fun a b => e * incA D ((δ : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))))
        (2 • actO V W h k c₀)) = 1 := by
  exact _root_.GlobalTheory.AdTh.MovedDatum.step_of_mem
    ψ hψ V W hV hr ΛV ΛW a1 a2 a3 a4 a5 l ι hι δ P e he hP bad N h k Λ mk hbad hh hΛ hT hL hmk Y hY q
    (fun LV LW x hX => one_sub_smul_mem_latO_pow V W LV LW e P he x fun s hs => (hq s hs).imp fun j hj => hX (s ^ j) hj) γ u hγ hu

end Lemmas

theorem moved_transSum : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW s f₀ → ∀ (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → ∀ (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ (r : ℕ) (hr : W.rank = r) (bad N : ℕ) (h : GA D V) (k : GA D W) (Λ : GenLat D.host.E V.rank) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), l₂.M ∣ bad → SplitOffBad V bad h → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (finPt V h)) → Λ.TrivAt l₂.M → Λ.LevOK N l₂.M → MarkAd l₂ W hr ι k mk → ∀ (Y : (Fin V.rank → LevQ Dw l₂) → Matrix (Fin V.rank) (Fin r) D.host.E) (γ : (Fin V.rank → LevQ Dw l₂) → Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : (Fin V.rank → LevQ Dw l₂) → WO V W), IsRoots l₂ (latR hr (latG W k)) mk N Y → (∀ q, colsR hr (γ q) = Y q ∧ IsFinOf V W (γ q) (u q)) → ∀ w : (Fin V.rank → LevQ Dw l₂) → ℂ, IsThetaFunO ψ V W (transSum ψ V W l₂ ι e f₀ w) ∧ om (h, k) (transSum ψ V W l₂ ι e f₀ w) = ((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin V.rank → LevQ Dw l₂, w q • heisO ψ V W (u q) (om (h, k) f₀) := by
  intro D H Dw ψ θ V W χV χW om ΛV ΛW s f₀ hvp ι hι l e hhalf r hr bad N h k Λ mk hbad hh hΛ hT hL hmk Y γ u hY hu w
  obtain ⟨hp, -, a1, a2, a3, a4, a5, -, hψ, hvac⟩ := hvp
  obtain ⟨P, he, hPiff⟩ := hhalf
  haveI : Finite (LevQ Dw l) := finite_levQ Dw l
  have hMb : ∀ PP ∈ P, ((l.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP =>
    (hPiff PP).1 hPP (natCast_mem_Mb l)
  have hPP : ∀ PP ∈ P, l.Mb ≤ PP.asIdeal ∧ (2 : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP
    refine ⟨(hPiff PP).1 hPP, fun h2 => PP.isPrime.one_notMem ?_⟩
    obtain ⟨m, hm⟩ := l.odd
    have h1 : ((l.M : ℕ) : 𝓞 D.host.E) - 2 * (m : 𝓞 D.host.E) = 1 := by rw [hm]; push_cast; ring
    rw [← h1]
    exact sub_mem (hMb PP hPP) (Ideal.mul_mem_right _ _ h2)
  have hbadP : ∀ PP ∈ P, ((bad : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    obtain ⟨c, rfl⟩ := hbad
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hMb PP hPP)
  have hq : ∀ q : Fin V.rank → LevQ Dw l, ∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∈ PP.asIdeal) →
      ∃ j : ℕ, ∀ b, ∃ z : Dw.La, s ^ j • (cSep l • levRep (q b)) = l.M • z := by
    intro q s hs
    obtain ⟨j, hj⟩ := exists_pow_mem_Mb l s fun PP hPP => hs PP ((hPiff PP).2 hPP)
    exact ⟨j, fun b => pow_sep l s j hj _⟩
  have key : ∀ q, om (h, k) (heisO ψ V W (levPoint V W l ι e q) f₀) = heisO ψ V W (u q) (om (h, k) f₀) := by
    intro q
    obtain ⟨c, hc, h1, h2⟩ := step_pow ψ hψ V W hp.std hr ΛV ΛW a1 a2 a3 a4 a5 l ι hι 1 P e he hPP bad N h k Λ mk hbadP hh
      hΛ hT hL hmk Y hY q (hq q) (γ q) (u q) (by rw [one_smul]; exact (hu q).1) (hu q).2
    have hlev : (Matrix.of fun a b => e * incA D (((1 : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) :
        WO V W) = levPoint V W l ι e q := by
      simp only [Int.cast_one, one_mul]; rfl
    rw [hlev] at h1 h2
    have h3 : heisO ψ V W (2 • actO V W h k c) (om (h, k) f₀) = om (h, k) f₀ := by
      rw [← actO_two, ← hp.weil.om_heis h k _ _ hvac.theta, hvac.lat.1 c hc]
    have h4 := GlobalTheory.PlaceModel.heisL_heisL V W ψ _ _ (om (h, k) f₀) |>.trans (congrArg (· • _) h2)
    rw [one_smul, ← h1] at h4
    rw [hp.weil.om_heis h k _ _ hvac.theta]
    refine Eq.trans ?_ h4
    exact congrArg _ h3.symm
  letI : Fintype (Fin V.rank → LevQ Dw l) := Fintype.ofFinite _
  refine ⟨?_, ?_⟩
  · unfold transSum
    apply GlobalTheory.OrientedHeis.theta_smul
    rw [finsum_eq_sum_of_fintype]
    exact Finset.sum_induction _ (IsThetaFunO ψ V W) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
      fun q _ => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hvac.theta _)
  · unfold transSum
    rw [map_smul, map_finsum _ (Set.toFinite _)]
    congr 1
    refine finsum_congr fun q => ?_
    rw [map_smul, key q]

end GlobalTheory.AdTh.MovedSum
