module

public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.ExistsIsomFrame
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapNeZeroOfMemHcompl
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
public import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
import Mathlib.Tactic.Linter.Style
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.GmapLocEqOfFrame

@[expose] public section

open NumberField Module

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3.WA
open Formalism.HermitianLattices.Ext.L3.WA (smul_mem_loc)
open Formalism.HermitianLatticesTheory
  (hcompl locBasic_le_locS locBasic_locS_idem locDual_mem_dualAt)

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem gmap_loc_eq_of_frame {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {p : Ideal (𝓞 K)} (hp : p.IsPrime) (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) {n : ℕ} {e : Fin n → V}
    (hspan : Submodule.span K (Set.range e) = ⊤)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hge : ∀ i, g (e i) ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p (Submodule.span (𝓞 K) (Set.range e))) =
      Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  have hg' : ∀ x y, h (g x) (g y) = h x y := hg
  apply le_antisymm
  · intro y hy
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨s, hs, hsx⟩ := hx
    have hN : Submodule.span (𝓞 K) (Set.range e) ≤
        (Formalism.HermitianLatticesTheory.loc (K := K) p L).comap ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hge i
    have h1 := hN hsx
    rw [Submodule.mem_comap, map_smul ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) s x] at h1
    rw [Formalism.HermitianLatticesTheory.loc, ← locBasic_locS_idem (hcompl (K := K) p) L]
    exact ⟨s, hs, h1⟩
  · intro y hy
    have hz : g.symm y ∈ Submodule.span K (Set.range e) := by
      rw [hspan]
      exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hz
    obtain ⟨c, hc⟩ := hz
    have hcj : ∀ j, c j ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
      intro j
      have e2 : h (g (e j)) y = h (e j) (g.symm y) := by
        conv_lhs => rw [← g.apply_symm_apply y]
        exact hg' _ _
      have e1 : c j = h (g (e j)) y := by
        rw [e2, ← hc]

        simp [map_sum, he]
      rw [e1]
      exact (locDual_mem_dualAt h p _ y).mp (by rw [hu]; exact hy) _ (hge j)
    have hzN : g.symm y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p (Submodule.span (𝓞 K) (Set.range e)) := by
      rw [← hc]
      refine sum_mem (fun i _ => ?_)
      exact smul_mem_loc hp (hcj i) (locBasic_le_locS _ _ (Submodule.subset_span ⟨i, rfl⟩))
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
    exact ⟨g.symm y, hzN, by simp⟩

end ReciprocityTheory.ChartRestriction.L3.WA
