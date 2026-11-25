module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairBundleTrdeg
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsAdjoinTrdegAdd
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairConeLinesIndep
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPairConeAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem trdeg_pointIdeal_bundle_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {d : ℕ}
    (hV : IsModelOver (pointIdeal O y) d) {M M' r : ℕ}
    {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
    {z : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ}
    (hzV : ∀ q : Σ k, ι k, z ⟨some (some q.1), q.2⟩ = algebraMap Ω Φ (y q))
    {l : Fin r → Fin M} {m' : Fin M'}
    (hadd : AdjoinTrdegAdd.Statement)
    (hind' : AlgebraicIndependent
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))
      (Sum.elim (fun i : Fin r => C (z ⟨some none, l i⟩) * X (some none))
        (fun _ : Unit => (C (z ⟨none, m'⟩) * X none : MvPolynomial (Option (Option K)) Φ))))
    (hal : ∀ p : Σ o, bundleIdx (bundleIdx ι M) M' o,
      IsAlgebraic (Algebra.adjoin O (Set.range (fun q : Σ k, ι k =>
        (C (algebraMap Ω Φ (y q)) * X (some (some q.1)) : MvPolynomial (Option (Option K)) Φ)) ∪
        Set.range (Sum.elim (fun i : Fin r => C (z ⟨some none, l i⟩) * X (some none))
          (fun _ : Unit => (C (z ⟨none, m'⟩) * X none : MvPolynomial (Option (Option K)) Φ)))))
        (C (z p) * X p.1)) :
    Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O z) =
      Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + ((r + 1 : ℕ) : Cardinal) := by
  let gV : (Σ k, ι k) → MvPolynomial (Option (Option K)) Φ :=
    fun q => C (algebraMap Ω Φ (y q)) * X (some (some q.1))
  let gZ : (Σ o, bundleIdx (bundleIdx ι M) M' o) → MvPolynomial (Option (Option K)) Φ :=
    fun p => C (z p) * X p.1
  let xs : Fin r ⊕ Unit → MvPolynomial (Option (Option K)) Φ :=
    Sum.elim (fun i : Fin r => C (z ⟨some none, l i⟩) * X (some none))
      (fun _ : Unit => C (z ⟨none, m'⟩) * X none)
  have hOΩ : Function.Injective (algebraMap O Ω) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hmem
    simpa using hmem
  have hOL : Function.Injective (algebraMap O (MvPolynomial (Option (Option K)) Φ)) := by
    rw [IsScalarTower.algebraMap_eq O Φ (MvPolynomial (Option (Option K)) Φ), IsScalarTower.algebraMap_eq O Ω Φ,
      MvPolynomial.algebraMap_eq]
    exact (C_injective _ _).comp ((algebraMap Ω Φ).injective.comp hOΩ)
  have hZ : Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O z) =
      Algebra.trdeg O (Algebra.adjoin O (Set.range gZ)) := by
    have e1 := (Ideal.quotientKerEquivRange (pointConeMap O z)).trdeg_eq
    have e2 : (pointConeMap O z).range = Algebra.adjoin O (Set.range gZ) := aeval_range _
    rw [e2] at e1
    exact e1
  have hw : AlgebraicIndependent Ω (fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) :=
    ((algebraicIndependent_X (Option (Option K)) Φ).restrictScalars (algebraMap Ω Φ).injective).comp _
      ((Option.some_injective _).comp (Option.some_injective _))
  let j : MvPolynomial K Ω →ₐ[O] MvPolynomial (Option (Option K)) Φ :=
    (aeval fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)).restrictScalars O
  have hjc : j.comp (pointConeMap O y) = aeval gV := by
    apply MvPolynomial.algHom_ext
    intro q
    simp [j, gV, pointConeMap, MvPolynomial.algebraMap_apply]
  have hV' : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = Algebra.trdeg O (Algebra.adjoin O (Set.range gV)) := by
    have e1 := (Ideal.quotientKerEquivRange (pointConeMap O y)).trdeg_eq
    have e2 := ((pointConeMap O y).range.equivMapOfInjective j hw).trdeg_eq
    rw [← AlgHom.range_comp, hjc, aeval_range] at e2
    exact e1.trans e2
  have hVZ : Set.range gV ⊆ Set.range gZ := by
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨some (some q.1), q.2⟩, by simp [gZ, gV, hzV q]⟩
  have hxZ : Set.range xs ⊆ Set.range gZ := by
    rintro _ ⟨i | _, rfl⟩
    · exact ⟨⟨some none, l i⟩, rfl⟩
    · exact ⟨⟨none, m'⟩, rfl⟩
  have hle : ∀ a ∈ Algebra.adjoin O (Set.range gV),
      a ∈ Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) := by
    intro a ha
    refine Algebra.adjoin_le (S := (Algebra.adjoin Ω (Set.range fun k : K =>
      (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))).restrictScalars O) ?_ ha
    rintro _ ⟨q, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
    have hc : (C (algebraMap Ω Φ (y q)) : MvPolynomial (Option (Option K)) Φ) ∈
        Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) := by
      rw [← MvPolynomial.algebraMap_apply]
      exact Subalgebra.algebraMap_mem _ _
    exact Subalgebra.mul_mem _ hc (Algebra.subset_adjoin ⟨q.1, rfl⟩)
  let f : Algebra.adjoin O (Set.range gV) →+*
      Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) :=
    { toFun := fun a => ⟨a, hle a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra (Algebra.adjoin O (Set.range gV))
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) :=
    f.toAlgebra
  have : IsScalarTower (Algebra.adjoin O (Set.range gV))
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))
      (MvPolynomial (Option (Option K)) Φ) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxind : AlgebraicIndependent (Algebra.adjoin O (Set.range gV)) xs :=
    hind'.restrictScalars (K := Algebra.adjoin Ω (Set.range fun k : K =>
      (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) fun a b h => Subtype.ext (congrArg Subtype.val h :)
  have key := hadd O (MvPolynomial (Option (Option K)) Φ) hOL (Set.range gV) (Set.range gZ) (Fin r ⊕ Unit) xs hxZ
    hxind (by rintro _ ⟨p, rfl⟩; exact hal p)
  rw [Set.union_eq_right.mpr hVZ] at key
  rw [hZ, hV', key, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]

theorem PairBundleTrdeg.proof (hadd : AdjoinTrdegAdd.Statement) (hind : PairConeLinesIndep.Statement)
    (halg : PairConeAlg.Statement) : PairBundleTrdeg.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht
  obtain ⟨l, m', hl, hm', hal⟩ :=
    halg O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht
  exact trdeg_pointIdeal_bundle_eq (z := pairProjCoord y e φ φ' t) hV (fun _ => rfl) hadd
    (hind Ω Φ K N E e (φ ∘ l) hl t ht _ hm') hal

end

end GroundTheory.Heights₂.Heights.NumbersDVR
