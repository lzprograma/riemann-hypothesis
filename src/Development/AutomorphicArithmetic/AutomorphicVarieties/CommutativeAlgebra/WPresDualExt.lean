module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PointsFinite
public import Mathlib.Algebra.DualNumber
public import Mathlib.Analysis.Normed.Field.Basic

@[expose] public section

open IsLocalRing UpperTheory.V.Alg

theorem UpperTheory.V.Alg.wpres_exists_dualNumber_extension {O X R K : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) [NormedField K]
    [Algebra O K] (hinj : Function.Injective (algebraMap O K)) (hw : ∀ x : K, ‖x‖ ≤ 1 → IsIntegral O x)
    (ξ : W.A →ₐ[O] DualNumber K) (h1 : ∀ x, ‖(ξ x).fst‖ ≤ 1) (hz : ∀ s, ‖(ξ (W.zA s)).fst‖ < 1)
    (hfg : ((W.gr 0).map ξ.toLinearMap).FG) :
    ∃ Ξ : R →ₐ[O] DualNumber K, (∀ x : W.A, Ξ x = ξ x) ∧ ∀ x, IsIntegral O (Ξ x) := by
  have hw' : ∀ x : DualNumber K, ‖x.fst‖ ≤ 1 → IsIntegral O x := fun x hx => by
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    refine IsIntegral.add ((hw _ hx).map (TrivSqZeroExt.inlAlgHom O K K)) ?_
    exact ⟨Polynomial.X ^ 2, Polynomial.monic_X_pow 2, by simp [pow_two]⟩
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp0 : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ hinj).2 hp.ne_zero
  let y : W.σ → DualNumber K := fun s => ξ (W.zA s)
  have hc : ∀ s, ∃ n : ℕ, IsIntegral O ((algebraMap O K p)⁻¹ • y s ^ n) := fun s => by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hp0) (hz s)
    refine ⟨n, hw' _ ?_⟩
    rw [TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_pow, smul_eq_mul, norm_mul, norm_inv, norm_pow, ← div_eq_inv_mul]
    exact div_le_one_of_le₀ hn.le (norm_nonneg _)
  choose e he using hc
  obtain ⟨T, hT⟩ := id hfg
  let G : Set (DualNumber K) := (T : Set _) ∪ Set.range y ∪ Set.range fun s => (algebraMap O K p)⁻¹ • y s ^ e s
  have hG : G.Finite := (T.finite_toSet.union (Set.finite_range _)).union (Set.finite_range _)
  have hGi : ∀ x ∈ G, IsIntegral O x := by
    rintro x ((hx | ⟨s, rfl⟩) | ⟨s, rfl⟩)
    · have : x ∈ (W.gr 0).map ξ.toLinearMap := hT ▸ Submodule.subset_span hx
      obtain ⟨a, -, rfl⟩ := this
      exact hw' _ (h1 a)
    · exact hw' _ (hz s).le
    · exact he s
  let B : Subalgebra O (DualNumber K) := Algebra.adjoin O G
  have : Module.Finite O B := Algebra.finite_adjoin_of_finite_of_isIntegral hG hGi
  have : IsNoetherianRing B := IsNoetherianRing.of_finite O B
  have := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal O) B
  let J : Ideal B := ((maximalIdeal O).map (algebraMap O B)).radical
  obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg ((maximalIdeal O).map (algebraMap O B))
    (IsNoetherian.noetherian _)
  have : IsAdicComplete J B :=
    { toIsHausdorff := GlobalTheory.NilpotentEval.isHausdorff_of_pow_le hN
      toIsPrecomplete := GlobalTheory.NilpotentEval.isPrecomplete_of_pow_le hN Ideal.le_radical }
  let yB : W.σ → B := fun s => ⟨y s, Algebra.subset_adjoin (Or.inl (Or.inr ⟨s, rfl⟩))⟩
  have hyB : ∀ s, yB s ∈ J := fun s => by
    refine ⟨e s, ?_⟩
    have : yB s ^ e s = algebraMap O B p *
        ⟨(algebraMap O K p)⁻¹ • y s ^ e s, Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)⟩ := by
      apply Subtype.ext
      show y s ^ e s = algebraMap O (DualNumber K) p * ((algebraMap O K p)⁻¹ • y s ^ e s)
      rw [← Algebra.smul_def, ← algebraMap_smul K p, smul_inv_smul₀ hp0]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hp.not_isUnit)
  obtain ⟨f, hf⟩ := wpres_factor_of_adic W ξ B.val 1 (GlobalTheory.mvEvalAdic O J yB hyB) Subtype.val_injective
    (fun s => by rw [GlobalTheory.mvEvalAdic_X]; simp [yB, y]) J (fun s => by rw [GlobalTheory.mvEvalAdic_X]; exact hyB s)
    (fun x hx => by
      have h1 : ξ x ∈ Submodule.span O (T : Set (DualNumber K)) := hT ▸ Submodule.mem_map_of_mem hx
      have h2 : Submodule.span O (T : Set (DualNumber K)) ≤ B.toSubmodule :=
        Submodule.span_le.2 fun a ha => Algebra.subset_adjoin (Or.inl (Or.inl ha))
      exact ⟨⟨ξ x, h2 h1⟩, rfl⟩)
  rw [wpres_act_one] at hf
  exact ⟨B.val.comp f, fun x => DFunLike.congr_fun hf x, fun x => (Algebra.IsIntegral.isIntegral (R := O) (f x)).map B.val⟩
