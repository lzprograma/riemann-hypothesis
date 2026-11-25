module

import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Mathlib.Tactic.Linter.Style

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

namespace GlobalTheory.HeckeComp

theorem smooth_loc {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.SmGL.IsSmoothChar (χ.loc w) := by
  apply _root_.GlobalTheory.Published.ParamAboveModel.smooth_loc

theorem eq_of_isComp {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {ξ ξ' : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : IsComp χ w ξ) (hξ' : IsComp χ w ξ') : ξ' = ξ := by
  have hs := hξ'.1.mul hξ.1.inv
  have hc := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 (MonoidHom.ext fun y => ?_)
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hc.isOpen_compl
  have hyU : (y : w.adicCompletion E) ∈ U := by
    have : y ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨y, hyU, y.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  show ξ' _ * (ξ _)⁻¹ = 1
  rw [hξ.2, hξ'.2]
  exact mul_inv_cancel _

theorem main : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)), ∃ ξ, IsComp χ w ξ ∧ (∀ ξ', IsComp χ w ξ' → ξ' = ξ) ∧ (χ.IsUnitary → ∀ x, ‖((ξ x : ℂˣ) : ℂ)‖ = 1) := by
  intro E _ _ χ w
  have hc : IsComp χ w (χ.loc w) := ⟨smooth_loc χ w, fun _ => rfl⟩
  exact ⟨χ.loc w, hc, fun ξ' h' => eq_of_isComp hc h', fun hu x => hu _⟩

end GlobalTheory.HeckeComp
