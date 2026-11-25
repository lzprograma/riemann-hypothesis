module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisCharacterPadicAlgClosureEqOne
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.Pst.DpstMap GlobalTheory.GalOfCusp

theorem UpperTheory.continuous_character_compact_unit_values :
    UpperTheory.V.Af.Wd.CharEnd := by
  intro F Ω _ _ _ _ _ l hl ι w A h hw ψ a hψ hσ
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have hq1 : 1 < normV w := GlobalTheory.WeilDeligne.one_lt_normV w
  have hpow := normV_eq_pow (l := l) hw
  have hf : resDeg l w ≠ 0 := by
    intro h0
    rw [hpow, h0, pow_zero] at hq1
    exact lt_irrefl _ hq1
  have hl1 : ‖(l : Qbar l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hlt : ‖((normV w : ℕ) : Qbar l)‖ < 1 := by
    rw [hpow, Nat.cast_pow, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hl1 hf
  have hpos : 0 < ‖((normV w : ℕ) : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (by omega))
  have ha : a = 0 := by
    have h1 := hσ (frob h)
    rw [deg_frob, mul_one, ← map_natCast ι, ← map_zpow₀] at h1
    have h2 := _root_.GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact
      ψ hψ (Subgroup.inclusion (Weil_le_Dec h) (frob h))
    rw [ι.injective h1, norm_zpow] at h2
    exact (zpow_eq_one_iff_right₀ hpos.le hlt.ne).1 h2
  refine ⟨ha, ?_⟩
  have hd := UpperTheory.weil_group_dense_in_galois_group F Ω w A h
  have he : (fun s => (ψ s : Qbar l)) = fun _ => 1 := by
    refine hd.equalizer hψ continuous_const (funext fun σ => ?_)
    have h1 := hσ σ
    rw [ha, zero_mul, zpow_zero, ← map_one ι] at h1
    exact ι.injective h1
  ext s
  simpa using congrFun he s
