module

import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
public import Formalism.SatakeDualWeyl.StatementE
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
import Mathlib.Algebra.Order.Star.Int

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.SplitResidueCard

theorem card_quotient_of_ncard {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    Nat.card (𝓞 F ⧸ v.asIdeal) = p := by
  have := v.isPrime
  have := v.isMaximal
  obtain ⟨w, hwm, hwo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hw : ((p : ℕ) : 𝓞 E) ∈ w := by
    have h1 : ((p : ℕ) : 𝓞 F) ∈ w.under (𝓞 F) := by rw [← hwo.over]; exact hv
    simpa using (show algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ w from h1)
  have hN : Nat.card (𝓞 E ⧸ w) = p := by
    rw [← GlobalTheory.LevDesc.absNorm_eq_of_split hp h hwm.isPrime hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hd : Nat.card (𝓞 F ⧸ v.asIdeal) ∣ p := by
    rw [← hN]
    exact AddSubgroup.card_dvd_of_injective (algebraMap (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w)).toAddMonoidHom
      (FaithfulSMul.algebraMap_injective (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w))
  refine ((Nat.dvd_prime hp).1 hd).resolve_left fun h1 => ?_
  have := (Nat.card_eq_one_iff_unique.1 h1).1
  exact not_subsingleton (𝓞 F ⧸ v.asIdeal) this

theorem card_kv : ∀ (D : D7) (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal → Nat.card (kv D.host.F v) = D.host.g i := by
  intro D i v hv
  rw [← card_quotient_of_ncard (D.host.g_prime i) (D.nd.g_split i) v hv]
  have h := Formalism.UG.P.tjcosets_card_residue v
  rw [h]
  simp [qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.SplitResidueCard
