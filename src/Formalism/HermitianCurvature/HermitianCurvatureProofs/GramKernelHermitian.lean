module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdicNeighbourhood
public import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.CoassocSimps

@[expose] public section

open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open Formalism.FourierDecayAlt.P.AdicNeighbourhood
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.A6x8

theorem iso_symm {K : Type} [CommRing K] (R : Subring K) {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K) (φ : coker R Z ≃ₗ[R] coker R Z') (hφ : φ ∈ isoZZ R Z Z') :
    φ.symm ∈ isoZZ R Z' Z := by
  refine ⟨by rw [← hφ.1]; simp, fun v' v hv => (hφ.2 v v' (by rw [← hv]; simp)).symm⟩

theorem iso_card {K : Type} [CommRing K] (R : Subring K) {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K) : Nat.card (isoZZ R Z' Z) = Nat.card (isoZZ R Z Z') :=
  Nat.card_congr
    { toFun := fun φ => ⟨φ.1.symm, iso_symm R Z' Z φ.1 φ.2⟩
      invFun := fun φ => ⟨φ.1.symm, iso_symm R Z Z' φ.1 φ.2⟩
      left_inv := by intro φ; ext; simp
      right_inv := by intro φ; ext; simp }

theorem kpHerm : KpHerm := by
  intro K _ R ψ w w'
  unfold Kp
  have h := AddMonoidHom.map_finsum_of_injective (starRingEnd ℂ).toAddMonoidHom
    (starRingEnd ℂ).injective (pairTerm R ψ w w')
  have h' : conj (∑ᶠ q, pairTerm R ψ w w' q) = ∑ᶠ q, conj (pairTerm R ψ w w' q) := h
  rw [h', ← finsum_comp_equiv (Equiv.prodComm (Cos R w) (Cos R w'))]
  refine finsum_congr fun q => ?_
  rcases q with ⟨q1, q2⟩
  show pairTerm R ψ w' w (q2, q1) = conj (pairTerm R ψ w w' (q1, q2))
  have hc := iso_card R (orbZ w (rep R q1)) (orbZ w' (rep R q2))
  unfold pairTerm
  by_cases h1 : IsInt R (orbZ w (rep R q1)) ∧ IsInt R (orbZ w' (rep R q2))
  · rw [ite_eq_left h1, ite_eq_left h1.symm, hc]; simp; ring
  · rw [ite_eq_right h1, ite_eq_right (fun h => h1 h.symm)]; simp

end Formalism.FourierDecayAlt.P.A6x8

namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood

section Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem small_add {Om : Set K} (hC : IsCompact Om) (hO : IsOpen Om) :
    ∃ W ∈ 𝓝 (0 : K), ∀ z ∈ Om, ∀ w ∈ W, z + w ∈ Om := by
  have hn : IsOpen ((fun p : K × K => p.1 + p.2) ⁻¹' Om) := hO.preimage continuous_add
  obtain ⟨u, v, -, hv, hsu, htv, huv⟩ :=
    generalized_tube_lemma hC (isCompact_singleton (x := (0 : K))) hn (by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      have hb' : b = 0 := hb
      simpa [hb'] using ha)
  exact ⟨v, hv.mem_nhds (htv rfl), fun z hz w hw => huv (Set.mk_mem_prod (hsu hz) hw)⟩

theorem small_scale {Om : Set K} (hC : IsCompact Om) (hO : IsOpen Om) :
    ∃ E ∈ 𝓝 (0 : K), ∀ z ∈ Om, ∀ κ : K, κ - 1 ∈ E → κ * z ∈ Om := by
  obtain ⟨W, hW, h1⟩ := small_add hC hO
  obtain ⟨E, hE, h2⟩ := small_mul hC hW
  refine ⟨E, hE, fun z hz κ hκ => ?_⟩
  have := h1 z hz _ (h2 _ hκ z hz)
  have e : z + (κ - 1) * z = κ * z := by ring
  rwa [e] at this

variable {R : Subring K} {ϖ : Kˣ}

theorem Adic.shift_small (h : Adic R ϖ) (Sg : Finset K) (a : Kˣ) :
    ∃ V ∈ 𝓝 (0 : K), ∀ t ∈ V, ∀ σ ∈ Sg, σ * t ∈ I R (a : K) := by
  refine ⟨⋂ σ ∈ Sg, (fun t => σ * t) ⁻¹' I R (a : K),
    (Filter.biInter_finset_mem Sg).2 fun σ _ => ?_, fun t ht σ hσ => ?_⟩
  · have : ContinuousAt (fun t : K => σ * t) 0 := (continuous_const.mul continuous_id).continuousAt
    exact this.preimage_mem_nhds (by simpa using I_nhds h.isOpen a)
  · exact Set.mem_iInter₂.1 ht σ hσ

theorem shift_alg (t t₁ : Kˣ) (σ : K) (h : IsShift t t₁ σ) :
    (t₁ : K) * (1 + σ * (t : K)) = (t : K) := by
  unfold IsShift at h
  have h1 : (t₁ : K) * ((t₁⁻¹ : Kˣ) : K) = 1 := by simp
  have h2 : ((t⁻¹ : Kˣ) : K) * (t : K) = 1 := by simp
  rw [h] at h1
  linear_combination (t : K) * h1 - (t₁ : K) * h2

theorem Adic.root_near (h : Adic R ϖ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (s : ℕ) (hs : 1 ≤ s)
    {E : Set K} (hE : E ∈ 𝓝 (0 : K)) :
    ∃ a : Kˣ, (a : K) ∈ I R (ϖ : K) ∧ ∀ b : K, Near R (a : K) b → ∃ κ : K, κ ^ s = b ∧ κ - 1 ∈ E := by
  obtain ⟨N, hN⟩ := h.basis E hE
  obtain ⟨u, hu⟩ := hn s (by omega)
  have hsR : (s : K) ∈ R := natCast_mem R s
  refine ⟨u ^ 2 * ϖ ^ (N + 1), ⟨(s : K) ^ 2 * (ϖ : K) ^ N,
    R.mul_mem (R.pow_mem hsR 2) (R.pow_mem h.mem N), by push_cast; rw [hu]; ring⟩, fun b hb => ?_⟩
  have hb' : Near R ((s : K) ^ 2 * (ϖ : K) ^ (N + 1)) b := by
    have e : ((u ^ 2 * ϖ ^ (N + 1) : Kˣ) : K) = (s : K) ^ 2 * (ϖ : K) ^ (N + 1) := by
      push_cast; rw [hu]
    rwa [e] at hb
  obtain ⟨κ, ⟨r, hr, e⟩, hκ⟩ := h.root s (c := (ϖ : K) ^ (N + 1))
    ⟨(ϖ : K) ^ N, R.pow_mem h.mem N, by ring⟩ hb'
  refine ⟨κ, hκ, ?_⟩
  have : κ - 1 = (ϖ : K) ^ N * ((ϖ : K) * (s : K) * r) := by rw [e]; ring
  rw [this]
  exact hN _ (R.mul_mem (R.mul_mem h.mem hsR) hr)

theorem Adic.inv_bounded (h : Adic R ϖ) {Om : Set K} (hC : IsCompact Om) (hU : ∀ z ∈ Om, IsUnit z) :
    ∃ M : ℕ, ∀ z ∈ Om, ∀ z' : K, z * z' = 1 → (ϖ : K) ^ M * z' ∈ R := by
  refine hC.induction_on
    (p := fun S => ∃ M : ℕ, ∀ z ∈ S, ∀ z' : K, z * z' = 1 → (ϖ : K) ^ M * z' ∈ R)
    ⟨0, by simp⟩ ?_ ?_ ?_
  · rintro S T hST ⟨M, hM⟩
    exact ⟨M, fun z hz => hM z (hST hz)⟩
  · rintro S T ⟨M, hM⟩ ⟨M', hM'⟩
    refine ⟨M + M', fun z hz z' e => ?_⟩
    rcases hz with hz | hz
    · have := R.mul_mem (R.pow_mem h.mem M') (hM z hz z' e)
      have e' : (ϖ : K) ^ (M + M') * z' = (ϖ : K) ^ M' * ((ϖ : K) ^ M * z') := by ring
      rwa [e']
    · have := R.mul_mem (R.pow_mem h.mem M) (hM' z hz z' e)
      have e' : (ϖ : K) ^ (M + M') * z' = (ϖ : K) ^ M * ((ϖ : K) ^ M' * z') := by ring
      rwa [e']
  · intro x hx
    obtain ⟨u, rfl⟩ := hU x hx
    obtain ⟨M, hM⟩ := h.absorb ((u⁻¹ : Kˣ) : K)
    refine ⟨{z | (z - (u : K)) * ((u⁻¹ : Kˣ) : K) ∈ I R (ϖ : K)}, mem_nhdsWithin_of_mem_nhds ?_, M,
      fun z hz z' e => ?_⟩
    · have : ContinuousAt (fun z : K => (z - (u : K)) * ((u⁻¹ : Kˣ) : K)) (u : K) :=
        ((continuous_id.sub continuous_const).mul continuous_const).continuousAt
      exact this.preimage_mem_nhds (by simpa using I_nhds h.isOpen ϖ)
    · obtain ⟨v, hv, ev⟩ := h.unit_one _ hz
      have i1 : (u : K) * ((u⁻¹ : Kˣ) : K) = 1 := by simp
      have : z' = ((u⁻¹ : Kˣ) : K) * v := by
        linear_combination ((u⁻¹ : Kˣ) : K) * v * e - z' * v * i1 - z' * ev
      rw [this, ← mul_assoc]
      exact R.mul_mem hM hv

end Top

end Formalism.FourierDecayAlt.P.AdicNeighbourhood

namespace Formalism.FourierDecayAlt.P.A6x8

theorem shiftUnit : ShiftUnit := by
  intro K _ _ _ R ψ hD hn Sg
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  obtain ⟨V, hV, hVs⟩ := h.shift_small Sg ϖ
  refine ⟨V, hV, fun t ht σ hσ => ?_⟩
  have hj := hVs _ ht σ hσ
  obtain ⟨v, hv, e⟩ := h.unit_one _ hj
  have hjR : 1 + σ * (t : K) ∈ R := by
    obtain ⟨r, hr, e'⟩ := hj
    rw [e']; exact R.add_mem R.one_mem (R.mul_mem h.mem hr)
  have hx : ((t⁻¹ : Kˣ) : K) + σ = ((t⁻¹ : Kˣ) : K) * (1 + σ * (t : K)) := by
    have : ((t⁻¹ : Kˣ) : K) * (t : K) = 1 := by simp
    linear_combination -σ * this
  rw [hx]
  refine ⟨(Units.isUnit _).mul (isUnit_iff_exists_inv.2 ⟨v, e⟩), ?_⟩
  have : mulR R (((t⁻¹ : Kˣ) : K) * (1 + σ * (t : K))) = mulR R ((t⁻¹ : Kˣ) : K) := by
    ext y
    simp only [mulR, AddSubgroup.mem_map, Subring.mem_toAddSubgroup, AddMonoidHom.coe_mulLeft]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(1 + σ * (t : K)) * r, R.mul_mem hjR hr, by ring⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨v * r, R.mul_mem hv hr, by linear_combination ((t⁻¹ : Kˣ) : K) * r * e⟩
  unfold modK
  rw [this]

theorem shiftSmall : ShiftSmall := by
  intro K _ _ _ R ψ hD hn Sg W hW
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  obtain ⟨V, hV, hVs⟩ := h.shift_small Sg ϖ
  obtain ⟨n, hn'⟩ := h.basis W hW
  refine ⟨V ∩ I R ((ϖ ^ n : Kˣ) : K), inter_mem hV (I_nhds h.isOpen _),
    fun t t₁ ht σ hσ hs => ?_⟩
  obtain ⟨v, hv, e⟩ := h.unit_one _ (hVs _ ht.1 σ hσ)
  obtain ⟨r, hr, e'⟩ := ht.2
  have h1 := shift_alg t t₁ σ hs
  have : (t₁ : K) = (ϖ : K) ^ n * (r * v) := by
    push_cast at e'
    linear_combination (-(t₁ : K)) * e + v * h1 + v * e'
  rw [this]
  exact hn' _ (R.mul_mem hr hv)

theorem rootCorr : RootCorr := by
  intro K _ _ _ R ψ hD hn m Sg E hE
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  obtain ⟨a, ha, hroot⟩ := h.root_near hn (m + 1) (by omega) hE
  obtain ⟨V, hV, hVs⟩ := h.shift_small Sg a
  refine ⟨V, hV, fun t t₁ t₂ ht σ hσ σ' hσ' hs hs' => ?_⟩
  have haR : (a : K) ∈ R := by
    obtain ⟨r, hr, e⟩ := ha
    rw [e]; exact R.mul_mem h.mem hr
  have n1 : Near R (a : K) (1 + σ * (t : K)) := by
    obtain ⟨r, hr, e⟩ := hVs _ ht σ hσ
    exact ⟨r, hr, by rw [e]⟩
  have n2 : Near R (a : K) (1 + σ' * (t : K)) := by
    obtain ⟨r, hr, e⟩ := hVs _ ht σ' hσ'
    exact ⟨r, hr, by rw [e]⟩
  obtain ⟨v, hv, nv, -⟩ := h.near_inv ha n2
  have a1 := shift_alg t t₁ σ hs
  have a2 := shift_alg t t₂ σ' hs'
  have hr : ((t₂ * t₁⁻¹ : Kˣ) : K) = (1 + σ * (t : K)) * v := by
    have i1 : (t₁ : K) * ((t₁⁻¹ : Kˣ) : K) = 1 := by simp
    rw [Units.val_mul]
    linear_combination (-((t₂ : K) * ((t₁⁻¹ : Kˣ) : K))) * hv + ((t₁⁻¹ : Kˣ) : K) * v * a2 -
      ((t₁⁻¹ : Kˣ) : K) * v * a1 + (1 + σ * (t : K)) * v * i1
  obtain ⟨κ, hκ, hκE⟩ := hroot _ ((n1.mul haR nv).pow haR m)
  rw [← hr, ← Units.val_pow_eq_pow_val] at hκ
  have hu : IsUnit κ := by
    have : IsUnit (κ ^ (m + 1)) := by rw [hκ]; exact Units.isUnit _
    exact (isUnit_pow_iff (by omega)).1 this
  obtain ⟨κ', rfl⟩ := hu
  exact ⟨κ', Units.ext (by rw [Units.val_pow_eq_pow_val, hκ]), hκE⟩

theorem cutSame : CutSame := by
  intro K _ _ _ R ψ hD hn m hm Om Sg hOm
  obtain ⟨hO, hC, hU, -⟩ := hOm
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  obtain ⟨E, hE, hscale⟩ := small_scale hC hO
  obtain ⟨a, ha, hroot⟩ := h.root_near hn (m + 1) (by omega) hE
  obtain ⟨V, hV, hVs⟩ := h.shift_small Sg a
  obtain ⟨M, hM⟩ := h.inv_bounded hC hU
  have haR : (a : K) ∈ R := by
    obtain ⟨r, hr, e⟩ := ha
    rw [e]; exact R.mul_mem h.mem hr
  have step : ∀ A b : K, Near R (a : K) b → (∃ z ∈ Om, z ^ (m + 1) = A) →
      ∃ z ∈ Om, z ^ (m + 1) = A * b := by
    rintro A b hb ⟨z, hz, rfl⟩
    obtain ⟨κ, hκ, hκE⟩ := hroot b hb
    exact ⟨κ * z, hscale z hz κ hκE, by rw [mul_pow, hκ]; ring⟩
  refine ⟨V ∩ I R ((a * ϖ ^ (M * (m + 1)) : Kˣ) : K), inter_mem hV (I_nhds h.isOpen _),
    fun t ht => ⟨fun σ hσ t₁ hs => ?_, fun c hc r hr => ?_⟩⟩
  · have n1 : Near R (a : K) (1 + σ * (t : K)) := by
      obtain ⟨r, hr, e⟩ := hVs _ ht.1 σ hσ
      exact ⟨r, hr, by rw [e]⟩
    obtain ⟨v, hv, nv, -⟩ := h.near_inv ha n1
    have a1 := shift_alg t t₁ σ hs
    have e1 : (t₁ : K) = (t : K) * v := by linear_combination (-(t₁ : K)) * hv + v * a1
    ext c
    constructor
    · intro hc
      have := step ((-(t₁ : K)) ^ m * c) _ (n1.pow haR m) hc
      have e2 : (-(t₁ : K)) ^ m * c * (1 + σ * (t : K)) ^ m = (-(t : K)) ^ m * c := by
        have e3 : -(t : K) = -(t₁ : K) * (1 + σ * (t : K)) := by linear_combination a1
        rw [e3, mul_pow]; ring
      rwa [e2] at this
    · intro hc
      have := step ((-(t : K)) ^ m * c) _ (nv.pow haR m) hc
      have e2 : (-(t : K)) ^ m * c * v ^ m = (-(t₁ : K)) ^ m * c := by rw [e1]; ring
      rwa [e2] at this
  · obtain ⟨z, hz, e⟩ := hc
    obtain ⟨u, rfl⟩ := hU z hz
    have hb := hM _ hz ((u⁻¹ : Kˣ) : K) (by simp)
    obtain ⟨r1, hr1, et⟩ := ht.2
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    push_cast at et
    have htR : (t : K) ∈ R := by
      rw [et]; exact R.mul_mem (R.mul_mem haR (R.pow_mem h.mem _)) hr1
    have nb : Near R (a : K)
        (1 + (-(t : K)) ^ (m' + 1) * r * ((u⁻¹ : Kˣ) : K) ^ (m' + 1 + 1)) :=
      ⟨-(r1 * (-(t : K)) ^ m' * r * ((ϖ : K) ^ M * ((u⁻¹ : Kˣ) : K)) ^ (m' + 1 + 1)),
        R.neg_mem (R.mul_mem (R.mul_mem (R.mul_mem hr1 (R.pow_mem (R.neg_mem htR) _)) hr)
          (R.pow_mem hb _)), by
        linear_combination (-((-(t : K)) ^ m' * r * ((u⁻¹ : Kˣ) : K) ^ (m' + 1 + 1))) * et⟩
    have := step _ _ nb ⟨u, hz, rfl⟩
    have i1 : (u : K) ^ (m' + 1 + 1) * ((u⁻¹ : Kˣ) : K) ^ (m' + 1 + 1) = 1 := by
      rw [← mul_pow]; simp
    have e2 : (u : K) ^ (m' + 1 + 1) *
        (1 + (-(t : K)) ^ (m' + 1) * r * ((u⁻¹ : Kˣ) : K) ^ (m' + 1 + 1)) =
        (-(t : K)) ^ (m' + 1) * (c + r) := by
      linear_combination e + (-(t : K)) ^ (m' + 1) * r * i1
    rwa [e2] at this

end Formalism.FourierDecayAlt.P.A6x8

alias Formalism.FourierDecayAlt.P.gramKernelHermitian := _root_.Formalism.FourierDecayAlt.P.A6x8.kpHerm

alias Formalism.FourierDecayAlt.P.shiftUnit_statement := _root_.Formalism.FourierDecayAlt.P.A6x8.shiftUnit

alias Formalism.FourierDecayAlt.P.shiftSmall_statement := _root_.Formalism.FourierDecayAlt.P.A6x8.shiftSmall

alias Formalism.FourierDecayAlt.P.rootCutStable := _root_.Formalism.FourierDecayAlt.P.A6x8.cutSame

alias Formalism.FourierDecayAlt.P.rootCorrection := _root_.Formalism.FourierDecayAlt.P.A6x8.rootCorr
