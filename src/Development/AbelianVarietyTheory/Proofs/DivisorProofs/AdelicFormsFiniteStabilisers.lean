module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegralFundamentalDomainEqSumDoubleCoset
import Formalism.LocalToGlobal.Columns.LevGCount
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace Pointwise

namespace GlobalTheory.InnerClassSum


open MeasureTheory IsDedekindDomain NumberField Matrix in
open scoped TensorProduct InnerProductSpace Pointwise in
theorem _root_.GlobalTheory.InnerClassSum.finite_stab_of_measure {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (h0 : ν K ≠ 0) (h1 : ν K ≠ ⊤) (a : G) :
    {γ : Γ | a⁻¹ * (γ : G) * a ∈ K}.Finite := by
  set S := {γ : Γ | a⁻¹ * (γ : G) * a ∈ K} with hS_def
  set T : Set G := (fun y => a⁻¹ * y) ⁻¹' (K : Set G) with hT_def
  have hT : ν T = ν K := measure_preimage_mul ν a⁻¹ K
  have hsum := h𝓖.measure_eq_tsum' T
  have hδT : ∀ δ ∈ S, δ • T = T := by
    intro δ hδ
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp only [hT_def, Set.mem_preimage, SetLike.mem_coe, Subgroup.smul_def, smul_eq_mul,
      Subgroup.coe_inv]
    have hk : a⁻¹ * (δ : G)⁻¹ * a ∈ K := by
      have := K.inv_mem hδ
      simpa [mul_assoc] using this
    constructor
    · intro hx
      have := K.mul_mem (K.inv_mem hk) hx
      simpa [mul_assoc] using this
    · intro hx
      have := K.mul_mem hk hx
      simpa [mul_assoc] using this
  have hinv : ∀ δ ∈ S, ∀ γ : Γ, ν (T ∩ (δ * γ) • 𝓖) = ν (T ∩ γ • 𝓖) := by
    intro δ hδ γ
    rw [← measure_smul ν δ (T ∩ γ • 𝓖), Set.smul_set_inter, hδT δ hδ, mul_smul]
  by_contra hinf
  obtain ⟨γ0, hγ0⟩ : ∃ γ0 : Γ, ν (T ∩ γ0 • 𝓖) ≠ 0 := by
    by_contra! hall
    apply h0
    rw [← hT, hsum]
    simp [hall]
  have hle := ENNReal.tsum_comp_le_tsum_of_injective (f := fun δ : S => (δ : Γ) * γ0)
    (fun x y hxy => Subtype.ext (mul_right_cancel hxy)) (fun γ : Γ => ν (T ∩ γ • 𝓖))
  have : Infinite S := Set.infinite_coe_iff.2 hinf
  have htop : ∑' δ : S, ν (T ∩ ((δ : Γ) * γ0) • 𝓖) = ⊤ := by
    rw [tsum_congr (fun δ : S => hinv δ δ.2 γ0)]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hγ0
  rw [htop, ← hsum, hT] at hle
  exact h1 (top_le_iff.1 hle)



end GlobalTheory.InnerClassSum
