module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeSupportLattices
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOnMemGoodPart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
public import Formalism.LocalToGlobal.ProjectiveLattices.AxHSupA
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeSup

section Grp

open Formalism.IndefR.Bridge GlobalTheory.HeckeModel

theorem exists_local_isDC {G : Type} [Group G] {J K L : Subgroup G} (hs : Splits J K L) {x : G} (hx : x ∈ L) {A : Finset G}
    (hA : IsDC J x A) : ∃ A₀, IsDC K x A₀ := by
  classical
  have hex : ∀ a : G, ∃ b : G, a ∈ A → (∃ k ∈ K, b = k * x) ∧ b⁻¹ * a ∈ J := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨k₁, k₂, rfl⟩ := hA.1 a ha
      obtain ⟨a₁, ha₁, b₁, hb₁, e₁, c₁⟩ := hs.dec k₁ k₁.2
      refine ⟨a₁ * x, fun _ => ⟨⟨a₁, ha₁, rfl⟩, ?_⟩⟩
      have : (a₁ * x)⁻¹ * ((k₁ : G) * x * k₂) = b₁ * k₂ := by
        rw [e₁, mul_assoc a₁ b₁ x, (c₁ x hx).eq]; group
      rw [this]
      exact J.mul_mem hb₁ k₂.2
    · exact ⟨1, fun h => absurd h ha⟩
  choose f hf using hex
  refine ⟨A.image f, fun b hb => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨k, hk, e⟩ := (hf a ha).1
    exact ⟨⟨k, hk⟩, 1, by simp [e]⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ⟨ha, hag⟩, hu⟩ := hA.2 ((k₁ : G) * x * k₂) ⟨⟨k₁, hs.le' k₁.2⟩, ⟨k₂, hs.le' k₂.2⟩, rfl⟩
    refine ⟨f a, ⟨Finset.mem_image_of_mem f ha, ?_⟩, ?_⟩
    · obtain ⟨k, hk, e⟩ := (hf a ha).1
      refine (hs.mem _ ?_).1 ?_
      · rw [e]
        exact L.mul_mem (L.inv_mem (L.mul_mem (hs.le hk) hx)) (L.mul_mem (L.mul_mem (hs.le k₁.2) hx) (hs.le k₂.2))
      · have := J.mul_mem (hf a ha).2 hag
        simpa [mul_assoc] using this
    · rintro b ⟨hb, hbg⟩
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 hb
      rw [hu a' ⟨ha', ?_⟩]
      have := J.mul_mem (J.inv_mem (hf a' ha').2) (hs.le' hbg)
      simpa [mul_assoc] using this

end Grp

section Geo

open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem nval_nonneg_of_int {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K'] [Algebra V K'] [IsFractionRing V K'] (e : ℕ) (a : V) : 0 ≤ nval V e (algebraMap V K' a) := by
  by_cases h0 : algebraMap V K' a = 0
  · rw [h0, nval_zero]; exact le_top
  rw [nval_of_ne h0]
  have hne : valV V (algebraMap V K' a) ≠ 0 := valV_ne_zero h0
  have hle : valV V (algebraMap V K' a) ≤ 1 :=
    (IsDiscreteValuationRing.maximalIdeal V).valuation_le_one a
  have hlog : WithZero.log (valV V (algebraMap V K' a)) ≤ 0 := by
    have := (WithZero.log_le_log hne one_ne_zero).2 hle
    simpa using this
  have hv : (0 : ℝ) ≤ (vV V (algebraMap V K' a) : ℝ) := by
    have : (0 : ℤ) ≤ vV V (algebraMap V K' a) := by simp only [vV]; omega
    exact_mod_cast this
  exact EReal.coe_nonneg.2 (div_nonneg hv (Nat.cast_nonneg e))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem transform_integral (hI : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeValueInt Xo c (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c))
    (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    {P : Ideal (𝓞 E)} {p i : ℕ} (hP : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p) (hF : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.FinKer Xo c P p i)
    {la : HeightOneSpectrum (𝓞 c.F)} (hp : (p : 𝓞 c.F) ∉ la.asIdeal) {s : c.F} (hs : la.valuation c.F s ≤ 1)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f g : Rul Xo c} (hf : f ∈ sec Xo c a n) (hg : g ∈ sec Xo c a n)
    (hr : HkRel (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)
      (fun Ω _ _ _ y C z => hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω y C z) s f g)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v g := by
  rintro _ ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  show 0 ≤ nval T.V e (evI y g)
  letI := io.toAlgebra
  let Ω := AlgebraicClosure T.Fr
  letI : Algebra c.F Ω := ((algebraMap T.Fr Ω).comp io).toAlgebra
  let k : T.Fr →ₐ[c.F] Ω := ⟨algebraMap T.Fr Ω, fun _ => rfl⟩
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1 E H Dw l Xo c _ _ k y.1
  have e1 : evR Xo c g z = k (evI y g) := evR_frMap hWD g hg.1 k y.1 y.2.1 z hz
  have e2 := hr Ω z
  haveI := hF Ω z
  set x := hkVal (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)
      (fun Ω _ _ _ y C z => hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω y C z) f z with hx
  have halg : (letI := k.toRingHom.toAlgebra; Algebra.IsAlgebraic T.Fr Ω) := by
    have hA : k.toRingHom.toAlgebra = (inferInstance : Algebra T.Fr Ω) := Algebra.algebra_ext _ _ fun _ => rfl
    rw [hA]
    exact AlgebraicClosure.isAlgebraic T.Fr
  have hint : IsIntegral T.V x := by
    rw [hx, hkVal]
    refine finsum_induction (IsIntegral T.V) isIntegral_zero (fun _ _ => IsIntegral.add) fun C => ?_
    unfold hkTerm
    split_ifs with h
    · exact (hI la P p i hP hp T io e ho y hy trivial Ω k halg z hz C _ h.choose_spec).2
        a n f hf h0
    · exact isIntegral_zero
  by_cases hs0 : s = 0
  · have : evI y g = 0 := by
      apply k.toRingHom.injective
      show k _ = k _
      rw [← e1, map_zero]
      refine e2.trans ?_
      rw [hs0, map_zero, zero_mul]
    rw [this, nval_zero]; exact le_top
  have e3 : algebraMap T.Fr Ω ((io s)⁻¹ * evI y g) = x := by
    rw [map_mul, map_inv₀]
    show (algebraMap c.F Ω s)⁻¹ * k _ = x
    rw [← e1]
    have : evR Xo c g z = algebraMap c.F Ω s * x := e2
    rw [this, inv_mul_cancel_left₀ ((map_ne_zero _).2 hs0)]
  rw [← e3, isIntegral_algebraMap_iff ] at hint
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have e4 : evI y g = io s * algebraMap T.V T.Fr w := by
    rw [hw, mul_inv_cancel_left₀ ((map_ne_zero _).2 hs0)]
  rw [e4, nval_smul ho hs0]
  refine add_nonneg ?_ (nval_nonneg_of_int e w)
  have h5 := (WithZero.log_le_log ((la.valuation c.F).ne_zero_iff.2 hs0) one_ne_zero).2 hs
  rw [WithZero.log_one] at h5
  have : (0 : ℤ) ≤ vLa la s := by unfold vLa; omega
  exact_mod_cast this

end Geo

end GlobalTheory.HeckeSup
