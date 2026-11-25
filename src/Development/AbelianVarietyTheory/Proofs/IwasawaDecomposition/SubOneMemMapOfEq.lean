module

import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertAtLeCongN
public import Formalism.LocalToGlobal.Columns.RowForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG Formalism.UG.P Formalism.EigenvalueLevelCeiling GlobalTheory.AdeleBaseChange
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwistPlaces

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valued_int {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) (b : 𝓞 K) :
    Valued.v (algebraMap K (P.adicCompletion K) (algebraMap (𝓞 K) K b)) = P.intValuation b := by
  rw [levelaf_valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]

theorem intValuation_eq_one {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) {b : 𝓞 K}
    (h : b ∉ P.asIdeal) : P.intValuation b = 1 :=
  le_antisymm (P.intValuation_le_one b) (not_lt.1 fun h' => h ((P.intValuation_lt_one_iff_mem b).1 h'))


variable (F E) in
abbrev toId : (RInt F E)ˣ →* (AfE F E)ˣ := Units.map (RInt F E).subtype.toMonoidHom

theorem exists_toId_eq {x : (AfE F E)ˣ} (hx : x ∈ intU F E) : ∃ u, toId F E u = x :=
  ⟨⟨⟨x, hx.1⟩, ⟨(x⁻¹ : (AfE F E)ˣ), hx.2⟩, Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩, Units.ext rfl⟩

section
variable {ι : AfE F E →+* FiniteAdeleRing (𝓞 E) E}
  (hι : ∀ x a, ι (x ⊗ₜ[F] a) = algebraMap E _ x * adMap F E a)
include hι

theorem mem_suppAt (v : HeightOneSpectrum (𝓞 F)) (y : (AfE F E)ˣ) :
    y ∈ suppAt E v ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ≠ v → ι (y : AfE F E) P = 1 := by
  have h1 : y ∈ suppAt E v ↔ ∀ v', v' ≠ v → prV (E := E) v' (y : AfE F E) = 1 := by
    simp only [suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  rw [h1]
  simp only [prV_eq_one_iff hι]
  exact ⟨fun h P hP => h _ hP P rfl, fun h v' hv P hP => h P (hP ▸ hv)⟩

end

theorem inertAt_le_congN {v : HeightOneSpectrum (𝓞 F)} {N : ℕ} (hN : (N : 𝓞 F) ∉ v.asIdeal) :
    inertAt E v ≤ congN F E N := by
  first | exact _root_.GlobalTheory.OpenChrRam.inertAt_le_congN | exact @_root_.GlobalTheory.OpenChrRam.inertAt_le_congN | apply _root_.GlobalTheory.OpenChrRam.inertAt_le_congN <;> assumption

variable {L : Type} [Field L]

theorem finite_Qprime {ξ : Chr F E L} (h : ξ ∈ openChr F E L) : (Qprime ξ).Finite := by
  obtain ⟨N, hN, hk⟩ := h
  have h0 : (Ideal.span {(N : 𝓞 F)}) ≠ ⊥ := by simpa using hN.ne'
  refine (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 (by_contra fun hn => hv ?_)
  exact (inertAt_le_congN hn).trans hk

end Local

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem under_eq_iff {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 F)} :
    P.under (𝓞 F) = v ↔ P.asIdeal.under (𝓞 F) = v.asIdeal :=
  ⟨fun h => h ▸ rfl, fun h => HeightOneSpectrum.ext h⟩

end Res

section Datum

open Formalism.L2.Col

variable {X : Fields}

theorem exists_of_conj_eq (hX : X.Ok) {a : 𝓞 X.E} (ha : X.conjO a = a) :
    ∃ r : 𝓞 X.F, algebraMap (𝓞 X.F) (𝓞 X.E) r = a := by
  let c : X.E →ₐ[X.F] X.E := { starRingEnd X.E with commutes' := hX.star_F }
  let M : IntermediateField X.F X.E :=
    (AlgHom.equalizer c (AlgHom.id _ _)).toIntermediateField fun x hx => by
      have hx' : star x = x := hx
      change star x⁻¹ = x⁻¹
      rw [star_inv₀, hx']
  have hM : M = ⊥ := by
    have := IntermediateField.isSimpleOrder_of_finrank_prime X.F X.E (by rw [hX.rankE]; exact Nat.prime_two)
    refine (eq_bot_or_eq_top M).resolve_right fun e => ?_
    obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hX.f_pos
    refine hX.emb_ne τ τ (RingHom.ext fun x => ?_)
    have h1 : x ∈ M := e ▸ IntermediateField.mem_top
    exact congrArg (X.emb τ) (show star x = x from h1).symm
  have h2 : (a : X.E) ∈ M := congrArg (fun z : 𝓞 X.E => (z : X.E)) ha
  rw [hM, IntermediateField.mem_bot] at h2
  obtain ⟨x, hx⟩ := h2
  have h3 : IsIntegral ℤ x := by
    rw [← isIntegral_algebraMap_iff (B := X.E), hx]
    exact RingOfIntegers.isIntegral_coe _
  exact ⟨⟨x, h3⟩, RingOfIntegers.ext hx⟩

variable {S : Set ℕ} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}

theorem mem_QE_iff (hsel : IsSel X sel) (ξ : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)} :
    P ∈ QE sel (ξ : Chr X.F X.E X.K) ↔
      P.under (𝓞 X.F) ∈ Qprime (ξ : Chr X.F X.E X.K) ∧ sel (P.under (𝓞 X.F)) = P := by
  classical
  have hf := finite_Qprime (ξ := (ξ : Chr X.F X.E X.K)) ξ.2.1.1.1.1.2
  rw [QE, dite_eq_left hf, Finset.mem_image]
  simp only [Set.Finite.mem_toFinset]
  refine ⟨?_, fun h => ⟨_, h.1, h.2⟩⟩
  rintro ⟨v, hv, rfl⟩
  rw [under_eq_iff.2 (hsel v)]
  exact ⟨hv, rfl⟩

end Datum

end GlobalTheory.TwistPlaces
