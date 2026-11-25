module

import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LineRank
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Mathlib.Tactic.Linter.Style

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

theorem UpperTheory.exists_unique_eigenline_of_rankOne_occurs :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)),
        IsSummand μ V → ∀ (w : Pl K) (τ : SmIrr (Gw n w)), Occurs μ V w τ → ∀ (J : Subgroup (Gw n w)) (χ : Gw n w → ℂ),
        CO J → IsChr J χ → RankOne μ V w J χ → V ⊓ eigL μ w J χ ≠ ⊥ →
        ∃ e : τ.V, e ≠ 0 ∧ (∀ g ∈ J, τ.ρ g e = χ g • e) ∧ ∀ x : τ.V, (∀ g ∈ J, τ.ρ g x = χ g • x) → ∃ c : ℂ, x = c • e := by
  intro K _ _ n μ _ V hV w τ hocc J χ hJ hχ hrk hne
  set P := prj (eigL μ w J χ) with hP
  let IsE : τ.V → Prop := fun x => ∀ g ∈ J, τ.ρ g x = χ g • x
  have hself : ∀ u ∈ eigL μ w J χ, P u = u := fun u hu =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ hu)
  have hE : ∀ y, ∃ y', IsE y' ∧ ∀ f : τ.V →ₗ[ℂ] LL μ, (∀ g x, f (τ.ρ g x) = rhoL μ w g (f x)) →
      P (f y) = f y' :=
    exists_vector_for_character_projection μ τ hJ hχ
  have hex : ∃ e, e ≠ 0 ∧ IsE e := by
    by_contra hno
    have hz : ∀ y, IsE y → y = 0 := fun y hy => by
      by_contra h
      exact hno ⟨y, h, hy⟩
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
    have h0 := eq_zero_on_summand_of_forall_intertwiner μ hV hocc P (fun f hf y => by
      obtain ⟨y', h1, h2⟩ := hE y
      rw [h2 f hf, hz y' h1, map_zero]) v hv.1
    exact hv0 ((hself v hv.2).symm.trans h0)
  obtain ⟨e, he0, he⟩ := hex
  refine ⟨e, he0, he, fun x hx => ?_⟩
  obtain ⟨f, hf0, hfV, hfi⟩ := hocc
  have hirr := (isIrreducible_iff τ.ρ).1 τ.irred
  have hinj : LinearMap.ker f = ⊥ := (hirr.2 _ (fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hfi, hv, map_zero])).resolve_right fun h => hf0 (LinearMap.ker_eq_top.1 h)
  have hfe : f e ∈ V ⊓ eigL μ w J χ :=
    ⟨hfV e, (mem_eigL_iff μ).2 fun g hg => by rw [← hfi, he g hg, map_smul]⟩
  set S : Submodule ℂ τ.V := Submodule.span ℂ (Set.range fun g => τ.ρ g e) with hSdef
  have heS : e ∈ S := Submodule.subset_span ⟨1, by simp⟩
  have hS : S = ⊤ := by
    refine (hirr.2 S fun g v hv => ?_).resolve_left fun h => he0 (by simpa [h] using heS)
    have h : S ≤ S.comap (τ.ρ g) := Submodule.span_le.2 (by
      rintro _ ⟨g', rfl⟩
      exact Submodule.subset_span ⟨g * g', by simp [map_mul]⟩)
    exact h hv
  have hSW : ∀ y ∈ S, ∃ c : ℂ, P (f y) = c • f e := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      obtain ⟨c, hc⟩ := hrk g
      exact ⟨c, by rw [hfi]; exact hc _ hfe⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c + d, by rw [map_add (f := _), map_add (f := _), hc, hd, add_smul]⟩
    | smul a b _ hb =>
      obtain ⟨c, hc⟩ := hb
      exact ⟨a * c, by rw [map_smul, map_smul, hc, smul_smul]⟩
  obtain ⟨c, hc⟩ := hSW x (hS ▸ Submodule.mem_top)
  have hfx : P (f x) = f x := hself _ ((mem_eigL_iff μ).2 fun g hg => by rw [← hfi, hx g hg, map_smul])
  refine ⟨c, LinearMap.ker_eq_bot.1 hinj ?_⟩
  rw [map_smul, ← hc, hfx]
