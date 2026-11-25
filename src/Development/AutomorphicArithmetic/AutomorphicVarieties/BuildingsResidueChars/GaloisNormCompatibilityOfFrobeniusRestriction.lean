module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValSubLtIff

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  apply _root_.GlobalTheory.DelEps.WeilRes.normV_eq_pow

private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have hl : l.Prime := Fact.out
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun v hv => ?_)
  exact Ideal.dvd_span_singleton.mpr (not_not.1 hv)

theorem UpperTheory.galois_norm_compatibility_of_frobenius_restriction :
    UpperTheory.V.Af.Bc.FrobRes → UpperTheory.V.Af.Bc.NormVal → UpperTheory.V.Af.Bc.NormGal := by
  intro hR hV E Ω _ _ _ _ _ _ l _ ι χ μ ⟨_, art, n, ha, _, h⟩
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under
      (maximalRealSubfield E) E).eventually
    ((Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified χ)).and (ev_notMem l))] with w ⟨hu, hl⟩
  have hf := normV_under (K := maximalRealSubfield E) w
  obtain ⟨h1, h2⟩ := hV E χ w _ hf hu
  refine ⟨h1, ?_⟩
  rw [h2, Units.val_pow_eq_pow_val]
  refine (hR (maximalRealSubfield E) E Ω l ι w _ hf).2 μ _ fun A hA => ⟨(h.unr_iff ha (Or.inl hl) hA).2 hu, fun σ hσ => ?_⟩
  rw [map_inv, Units.val_inv_eq_inv_val, h.frob_unr ha (Or.inl hl) hu hA hσ, inv_inv, RingEquiv.apply_symm_apply]
