module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RamFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocGood
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnivEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnivQuot
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Connected.Separation
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PhiCondOfFiniteH1

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.U3

private theorem phi_surj {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (π : Γ →* Γ')
    (hc : Continuous π) (hπ : Function.Surjective π) {l : ℕ} (h : PhiCond Γ l) : PhiCond Γ' l := fun H hH => by
  haveI := h (H.comap π) (hH.preimage hc)
  let p : H.comap π →* H := π.subgroupComap H
  have hp : Continuous p := (hc.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective p := MonoidHom.subgroupComap_surjective_of_surjective _ _ hπ
  refine Finite.of_injective
    (β := {φ : H.comap π →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set (H.comap π))})
    (fun φ => ⟨φ.1.comp p, φ.2.preimage hp⟩) fun φ φ' e => ?_
  exact Subtype.ext ((MonoidHom.cancel_right hs).1 (congrArg Subtype.val e))

private theorem phi_unr (hGF : GlobalFiniteness) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    [hl : Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : ContainsAbove S l) (M : Subgroup (G ℚ Ω)) [M.Normal]
    (hM : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ M) : PhiCond (G ℚ Ω ⧸ M) l := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI hK : CompactSpace (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) := inferInstance
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have key : PhiCond (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) (l ^ 1) := UpperTheory.V.Alg.phiCond_of_finite_H1 (l ^ 1) fun M _ _ _ _ _ ρ hρ => by
    obtain ⟨-, f1, -⟩ := hGF ℚ Ω l 1 M S ρ one_pos hS hρ
    exact f1
  rw [pow_one] at key
  refine phi_surj (QuotientGroup.lift _ (QuotientGroup.mk' M) fun g hg => (QuotientGroup.eq_one_iff g).2 (hM hg))
    ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 continuous_quotient_mk') (fun y => ?_) key
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨QuotientGroup.mk g, rfl⟩

end UpperTheory.V.U3

theorem UpperTheory.V.U3.exists_ring :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))) (g₁ : G ℚ Ω), D.Marked g₁ → Nonempty (D.Ring U g₁) := by
  intro hI Ω _ _ _ K _ _ _ l hl c N hN e ψ D U g₁ hg₁
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨hc, hf, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI := hc
  haveI : Finite (ResidueField c.O) := hf
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]; exact hlm)
  obtain ⟨-, -, -, hη, hΨ, hK, -, -, -, hKill, -⟩ := dat_facts D
  haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨T, hT⟩ := (ramFinite ℚ ℚ K Ω).1
  obtain ⟨-, -, -, -, hIne⟩ := Chr.clsFacts ℚ Ω N
  have hfin : {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Ideal.span {((l * N : ℕ) : 𝓞 ℚ)}}.Finite :=
    Ideal.finite_factors (by simpa using ⟨hl.out.ne_zero, hN.out⟩)
  classical
  have hmem : ∀ v, ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ T ∪ hfin.toFinset := fun v hv =>
    Finset.mem_union_right _ (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 hv))
  have hval : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v → ∀ n : ℕ,
      A.valuation (n : Ω) < 1 → ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro A v hv n hn
    have h := hv ((n : ℕ) : 𝓞 ℚ)
    have e : algebraMap ℚ Ω (((n : ℕ) : 𝓞 ℚ) : ℚ) = (n : Ω) := by simp
    rw [e] at h
    exact h.1 hn
  haveI : (Subgroup.normalClosure D.Kill).topologicalClosure.Normal := Subgroup.is_normal_topologicalClosure _
  have hΦ : PhiCond (G ℚ Ω ⧸ (Subgroup.normalClosure D.Kill).topologicalClosure) l := by
    refine phi_unr hI.gf l (T ∪ hfin.toFinset) (fun v hv => hmem v ?_) _
      (Subgroup.topologicalClosure_mono (Subgroup.normalClosure_mono fun g hg => ?_))
    · rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hv
    · simp only [Set.mem_iUnion] at hg
      obtain ⟨v, hv, A, hA, hg⟩ := hg
      have hv' : ((l * N : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hmem v h)
      rw [Nat.cast_mul] at hv'
      refine (hKill g).2 ⟨A, fun h => hv' (v.asIdeal.mul_mem_right _ (hval A v hA l h)), hg, ?_, ?_⟩
      · rw [← MonoidHom.mem_ker, D.η_ker]
        exact hT v (fun h => hv (Finset.mem_union_left _ h)) A hA ⟨by rw [galOf_self]; trivial, hg⟩
      · have h1 : Chr.cls ℚ Ω N g = 1 := hIne A (fun h => hv' (v.asIdeal.mul_mem_left _ (hval A v hA N h))) hg
        simp only [Chr.dirG, MonoidHom.comp_apply, h1, map_one]
  exact (exists_sRing D.ι_cont U (D.loc.It U) D.cc g₁ hg₁ (Loc.locGood hI.loc D.loc U) D.Ψ_cont hK
    (exists_univ l D.η D.Ψ hη hΨ D.Kill (fun g ⟨_, _, _, h⟩ => h) _ rfl hΦ)).2
