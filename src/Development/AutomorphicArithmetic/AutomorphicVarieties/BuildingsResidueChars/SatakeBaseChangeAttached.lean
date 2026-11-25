module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowerCompatibility
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsQuadCharOfOfIsNormChar
import Mathlib.NumberTheory.RamificationInertia.Inertia

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem algSat_pow_map_pow (n q f : ℕ) (B : Multiset ℂˣ) : algSat n (q ^ f) (Multiset.map (fun x => x ^ f) B) = Multiset.map (fun x => x ^ f) (algSat n q B) := by
  unfold algSat
  simp only [Multiset.map_map, Function.comp_def, Multiset.bind_singleton, Multiset.pure_def, Multiset.bind_def]
  refine Multiset.map_congr rfl fun b _ => ?_
  rw [mul_pow]
  congr 1
  push_cast
  rw [← Complex.ofReal_pow, Real.rpow_pow_comm (by positivity)]

theorem UpperTheory.satake_base_change_attached :
    UpperTheory.V.Af.Sol.AttBc := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι n r sat sat' huniq hbc hatt hss
  refine ⟨hss, ?_⟩
  have hT := UpperTheory.frobenius_power_compatibility K M Ω l ι
  have htend := GlobalTheory.QuadNormChar.tendsto_under (K := K) (K' := M)
  filter_upwards [hbc, htend.eventually hatt.2] with w hw hv
  set f := w.asIdeal.inertiaDeg (𝓞 K)
  have hf := GlobalTheory.QuadNormChar.normV_under (K := K) w
  obtain ⟨B, hB, hE⟩ := hv
  obtain ⟨B0, hB0, hB0'⟩ := hw f hf
  obtain rfl := huniq _ _ _ hB hB0
  refine ⟨_, hB0', ?_⟩
  have h2 := (hT w f hf).1 n r _ hE
  rw [hf, algSat_pow_map_pow]
  exact h2
