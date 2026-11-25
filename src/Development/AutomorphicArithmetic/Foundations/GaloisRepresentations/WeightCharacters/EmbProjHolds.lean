module

import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Prelims.ProjEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedean
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

theorem embProj_holds : EmbProj := by
  intro E _ _ _ a τ U hU κ hκ u hu hu0
  obtain ⟨e, he⟩ := _root_.GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E a τ
  obtain ⟨r, -, hr1, hr⟩ := _root_.GlobalTheory.DefU.exists_embRet E a τ
  let π : AutSub E a := ⟨U, hU⟩
  let s : Matrix.unitaryGroup (Fin a) ℂ →* UA E a := (embU a τ).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hs : ∀ y, cEmb τ (s y) = unitaryIncl a y := fun y => by
    have h3 := he (e.symm y)
    rw [e.apply_symm_apply] at h3
    exact h3.symm
  have hirr := isIrreducible_smallRep_unitary a κ
  obtain ⟨-, hsimple⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hirr
  let S : Set (Submodule ℂ (UA E a → ℂ)) := {V | ∃ F : nablaSq ℂ a κ →ₗ[ℂ] (UA E a → ℂ), Function.Injective F ∧ (∀ w, F w ∈ U) ∧
    (∀ y w, F (sqRep ℂ a κ (unitaryIncl a y) w) = RU E a (s y) (F w)) ∧ V = LinearMap.range F}
  have hc : ∀ g, ∃ y, ∀ y', Commute ((s y)⁻¹ * g) (s y') := fun g =>
    ⟨e (r g), fun y => by
      change Commute ((((e.symm (e (r g))) : embU a τ) : UA E a)⁻¹ * g) ((e.symm y : embU a τ) : UA E a)
      rw [e.symm_apply_apply]
      exact hr g _⟩
  obtain ⟨f, hf⟩ : ∃ f : (smallRep (unitaryIncl a) κ).IntertwiningMap (π.rep.comp s), f ≠ 0 := by
    obtain ⟨-, F, hF0, hFm, hFi⟩ := hκ
    refine ⟨⟨F.codRestrict U hFm, fun y => ?_⟩, fun h0 => hF0 ?_⟩
    · ext v : 1
      apply Subtype.ext
      show F (sqRep ℂ a κ (unitaryIncl a y) v) = RU E a (s y) (F v)
      rw [← hs y]
      exact hFi (e.symm y) v
    · ext v : 1
      exact congrArg Subtype.val (DFunLike.congr_fun h0 v :)
  have htop := (_root_.GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ _ π.rep s _ _ π.isIrreducible_rep hirr hirr hc f hf).1
  have hUS : U ≤ sSup S := by
    intro φ hφ
    have h1 : (⟨φ, hφ⟩ : U) ∈ (⨆ f : (smallRep (unitaryIncl a) κ).IntertwiningMap (π.rep.comp s), LinearMap.range f.toLinearMap) :=
      htop ▸ Submodule.mem_top
    refine (iSup_le (a := (sSup S).comap U.subtype) fun f' => ?_) h1
    rintro _ ⟨w, rfl⟩
    let F : nablaSq ℂ a κ →ₗ[ℂ] (UA E a → ℂ) := U.subtype ∘ₗ f'.toLinearMap
    have hF : ∀ y w, F (sqRep ℂ a κ (unitaryIncl a y) w) = RU E a (s y) (F w) := fun y w =>
      congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ f' y w)
    show F w ∈ sSup S
    rcases hsimple (LinearMap.ker F) (fun y x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      exact (hF y x).trans (by rw [hx, map_zero])) with h | h
    · exact le_sSup (show LinearMap.range F ∈ S from ⟨F, LinearMap.ker_eq_bot.1 h, fun w => (f' w).2, hF, rfl⟩) ⟨w, rfl⟩
    · have : w ∈ LinearMap.ker F := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker.1 this]
      exact zero_mem _
  obtain ⟨_, ⟨F, hinj, hFU, hF, rfl⟩, pr, h1, h2⟩ := UpperTheory.TP.proj_of_sum (fun y => RU E a (s y)) U S
    (by rintro _ ⟨F, -, hFU, -, rfl⟩ _ ⟨w, rfl⟩; exact hFU w)
    (by rintro _ ⟨F, -, -, hF, rfl⟩ y _ ⟨w, rfl⟩; exact ⟨_, hF y w⟩)
    (by
      rintro _ ⟨F, -, -, hF, rfl⟩ N hN hNs
      rcases hsimple (N.comap F) (fun y x hx => by
        show F _ ∈ N
        exact (hF y x).symm ▸ hNs y _ hx) with h | h
      · left
        rw [eq_bot_iff]
        intro φ hφ
        obtain ⟨w, rfl⟩ := hN hφ
        have : w ∈ N.comap F := hφ
        rw [h, Submodule.mem_bot] at this
        rw [this, map_zero]
        exact zero_mem _
      · right
        refine le_antisymm hN ?_
        rintro _ ⟨w, rfl⟩
        exact (h ▸ Submodule.mem_top : w ∈ N.comap F))
    hUS u hu hu0
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective F (LinearMap.ker_eq_bot.2 hinj)
  have hGF : ∀ w, G (F w) = w := fun w => LinearMap.congr_fun hG w
  refine ⟨G ∘ₗ pr, fun h0 => h1 ?_, fun x hx y hy => ?_⟩
  · obtain ⟨w, hw⟩ := (h2 u hu).1
    rw [LinearMap.comp_apply, ← hw, hGF] at h0
    rw [← hw, h0, map_zero]
  · obtain ⟨w, hw⟩ := (h2 y hy).1
    have hx' : s (e ⟨x, hx⟩) = x := congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
    have h3 := (h2 y hy).2 (e ⟨x, hx⟩)
    rw [← hw, ← hF, ← hs, hx'] at h3
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h3, ← hw, hGF, hGF]

end UpperTheory.Gal.Wt

end
