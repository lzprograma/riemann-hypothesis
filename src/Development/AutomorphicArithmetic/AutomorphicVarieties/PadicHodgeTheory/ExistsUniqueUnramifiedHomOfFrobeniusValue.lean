module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedCocycleFrobeniusValue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaFacts
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply

@[expose] public section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

theorem UpperTheory.exists_unique_unramified_hom_of_frobenius_value :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (v : ℕ), v.Prime → ∀ (A : ValuationSubring Ω), A.valuation (v : Ω) < 1 → ∀ σ : ↥(Dec (F := ℚ) A), Formalism.ConjugateSelfDual.IsFrob (F := ℚ) A v (σ : G ℚ Ω) → ∀ (E : Type) [AddCommGroup E] [Module ℚ_[l] E] [Module.Finite ℚ_[l] E], (∀ e : E, ∃ u : ↥(Dec (F := ℚ) A) → E, QCont l u ∧ (∀ g h, u (g * h) = u g + u h) ∧ (∀ g : ↥(Dec (F := ℚ) A), (g : G ℚ Ω) ∈ Ine (F := ℚ) A → u g = 0) ∧ u σ = e) ∧ ∀ u : ↥(Dec (F := ℚ) A) → E, QCont l u → (∀ g h, u (g * h) = u g + u h) → (∀ g : ↥(Dec (F := ℚ) A), (g : G ℚ Ω) ∈ Ine (F := ℚ) A → u g = 0) → u σ = 0 → u = 0 := by
  intro Ω _ _ _ l _ v hv A hA σ hσ E _ _ _
  haveI : Fact v.Prime := ⟨hv⟩
  obtain ⟨w, hwv, hwA⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (UpperTheory.V.Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).1 _ w hwA hwv
  obtain ⟨hemb, hrange, hcomap, -, -, -, hfrob⟩ := UpperTheory.V.Loc.iotaFacts (v := v) j
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalAddGroup E := IsModuleTopology.topologicalAddGroup ℚ_[l] E
  let ρ : Representation ℚ_[l] (Formalism.BasicNotions.Loc.GQ v) E := Representation.trivial ℚ_[l] _ E
  have hρ : ∀ g x, ρ g x = x := fun _ _ => rfl
  have hcont : ContAction ρ := by
    show Continuous fun p : Formalism.BasicNotions.Loc.GQ v × E => ρ p.1 p.2
    simp only [hρ]
    exact continuous_snd
  have hI : ∀ g ∈ Iq v, ρ g = 1 := fun _ _ => rfl
  have hmem : ∀ c : Formalism.BasicNotions.Loc.GQ v → E,
      c ∈ Z1 ρ ↔ Continuous c ∧ ∀ g h, c (g * h) = c g + c h := by
    intro c
    exact Iff.rfl
  let φ : Formalism.BasicNotions.Loc.GQ v ≃* ↥(Dec (F := ℚ) (placeJ j)) :=
    (MonoidHom.ofInjective hemb.injective).trans (MulEquiv.subgroupCongr hrange)
  have hφ_symm_val : ∀ g, iota j (φ.symm g) = g := fun g =>
    congrArg Subtype.val (φ.apply_symm_apply g)
  have hφ_cont : Continuous φ := continuous_induced_rng.2 hemb.continuous
  have hφ_symm_cont : Continuous φ.symm := by
    rw [hemb.isInducing.continuous_iff]
    have hfun : (iota j ∘ φ.symm) = fun g : ↥(Dec (F := ℚ) (placeJ j)) => (g : G ℚ Ω) :=
      funext hφ_symm_val
    rw [hfun]
    exact continuous_subtypeVal
  let τ := φ.symm σ
  have hτF : UpperTheory.V.Loc.IsFrob τ := (hfrob τ).2 (hφ_symm_val σ ▸ hσ)
  have hIq : ∀ x, x ∈ Iq v ↔ iota j x ∈ Ine (F := ℚ) (placeJ j) := by
    intro x
    rw [← hcomap]
    rfl
  refine ⟨?_, ?_⟩
  · intro e
    obtain ⟨c, ⟨hcZ, hcI, hcσ⟩, -⟩ := UpperTheory.V.Loc.existsUnique_unramified_cocycle_frobenius_value (l := l) (A := ℚ_[l]) ρ hcont hI τ hτF e
    obtain ⟨hcc, hcm⟩ := (hmem c).1 hcZ
    refine ⟨fun g => c (φ.symm g), ?_, ?_, ?_, ?_⟩
    · exact hcc.comp hφ_symm_cont
    · intro g h
      simp only [map_mul, hcm]
    · intro g hg
      apply hcI
      rw [hIq, hφ_symm_val]
      exact hg
    · exact hcσ
  · intro u hu hum huI huσ
    obtain ⟨c0, -, huniq⟩ := UpperTheory.V.Loc.existsUnique_unramified_cocycle_frobenius_value (l := l) (A := ℚ_[l]) ρ hcont hI τ hτF 0
    have hc : (fun x => u (φ x)) = 0 := by
      have h1 : (fun x => u (φ x)) = c0 := by
        apply huniq
        refine ⟨(hmem _).2 ⟨hu.comp hφ_cont, ?_⟩, ?_, ?_⟩
        · intro g h
          simp only [map_mul, hum]
        · intro g hg
          exact huI _ ((hIq g).1 hg)
        · simp only [τ, φ.apply_symm_apply, huσ]
      have h2 : (0 : Formalism.BasicNotions.Loc.GQ v → E) = c0 := by
        apply huniq
        refine ⟨(hmem _).2 ⟨continuous_const, ?_⟩, ?_, ?_⟩
        · intro g h
          simp
        · intro g _
          rfl
        · rfl
      rw [h1, h2]
    funext g
    have := congrFun hc (φ.symm g)
    simp only [φ.apply_symm_apply] at this
    exact this
