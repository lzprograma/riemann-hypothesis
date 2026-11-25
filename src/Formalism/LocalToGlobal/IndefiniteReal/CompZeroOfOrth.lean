module

public import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
public import Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Dec

local instance instCMHostD (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

def IsotDecomp (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  Mult.goodPart θ M J χ e = ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, isotL θ P M J χ e π ∧
    ∀ π π' : Formalism.L2.NG.FinTyp D.host.E n, ¬ π.Iso π' →
      ∀ x ∈ isotL θ P M J χ e π, ∀ y ∈ isotL θ P M J χ e π', Mult.ipM M μ 𝓕 x y = 0

end Dec

section DecProofs

local instance instCMHostD' (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
variable {P : RowPsi V n} {M : Mult.DSModel V Sp}

theorem isMultMap_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k)
    {T : Mult.MMap M} (h : Mult.IsMultMap θ M J χ T) : Mult.IsMultMap θ M J' χ' T :=
  ⟨h.aut, h.cusp, fun v k hk g => by rw [h.lev v k (hJ hk) g, hχ k hk], h.equiv, h.cont⟩

theorem mult_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k) :
    Mult.Mult θ M J χ ≤ Mult.Mult θ M J' χ' :=
  Submodule.span_mono fun _ hT => isMultMap_mono hJ hχ hT

theorem levN_mono (N m : ℕ) : levN P (N * m) ⊆ levN P N := by
  rintro _ ⟨κ, hκ, rfl⟩
  exact ⟨κ, Formalism.L2.NG.Cong.of_mul_left D.host.E n hκ, rfl⟩

abbrev LN (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (P : RowPsi V n) (M : Mult.DSModel V Sp) (N : ℕ) :
    Submodule ℂ (Mult.MMap M) :=
  Mult.Mult θ M (levN P (N + 1)) (fun _ => 1)

theorem LN_directed : Directed (· ≤ ·) (LN θ P M) := by
  intro i j
  have hpos : 1 ≤ (i + 1) * (j + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have e : (i + 1) * (j + 1) - 1 + 1 = (i + 1) * (j + 1) := Nat.sub_add_cancel hpos
  refine ⟨(i + 1) * (j + 1) - 1, ?_, ?_⟩
  · apply mult_mono
    · rw [e]
      exact levN_mono _ _
    · intros
      rfl
  · apply mult_mono
    · rw [e, mul_comm]
      exact levN_mono _ _
    · intros
      rfl

theorem mem_Minf {T : Mult.MMap M} : T ∈ Minf θ P M ↔ ∃ N, T ∈ LN θ P M N :=
  Submodule.mem_iSup_of_directed _ LN_directed

theorem LN_le_Minf (N : ℕ) : LN θ P M N ≤ Minf θ P M := le_iSup (LN θ P M) N

theorem mult_le_Minf {J : Set (GA D V)} {χ : GA D V → ℂ} (hl : LevOK P J χ) : Mult.Mult θ M J χ ≤ Minf θ P M := by
  obtain ⟨N0, hN0, h0⟩ := hl
  have e : N0 - 1 + 1 = N0 := Nat.sub_add_cancel hN0
  refine le_trans ?_ (LN_le_Minf (N0 - 1))
  apply mult_mono
  · rintro _ ⟨κ, hκ, rfl⟩
    rw [e] at hκ
    exact (h0 κ hκ).1
  · rintro _ ⟨κ, hκ, rfl⟩
    rw [e] at hκ
    exact (h0 κ hκ).2.symm

end DecProofs

end Formalism.IndefR.principalLevelFrame
