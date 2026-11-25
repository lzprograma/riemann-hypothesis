module

public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.EqZeroOfNegEq
public import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Mathlib.Order.CompletePartialOrder
public import Formalism.LocalToGlobal.UnitaryNorms.Lemmas
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open IntermediateField NumberField

namespace Formalism.HC.HostRaw

open Formalism.FrobeniusOrbits Formalism.L2.Host

variable {φ : Frame} (H : HostRaw φ)

def EQ : Fld := ⨆ j : H.E →ₐ[ℚ] Qb, j.fieldRange

def FI : IntermediateField ℚ H.E := H.F.toIntermediateField fun x => by
  simp

def FQ : Fld := ⨆ j : H.E →ₐ[ℚ] Qb, H.FI.map j

theorem mem_EQ (j : H.E →ₐ[ℚ] Qb) (x : H.E) : j x ∈ H.EQ :=
  (le_iSup (fun j : H.E →ₐ[ℚ] Qb => j.fieldRange) j) ⟨x, rfl⟩

def ActsAs (s : H.EQ →ₐ[ℚ] Qb) (g : φ.GG) : Prop :=
  ∀ (j : H.E →ₐ[ℚ] Qb) (x : H.E), s ⟨j x, H.mem_EQ j x⟩ = j (H.gal.symm g x)

def CondEQ : Prop := IsCond H.EQ H.condN

theorem nonempty_emb : Nonempty (H.E →ₐ[ℚ] Qb) := ⟨IsAlgClosed.lift⟩

theorem exists_aut (j j' : H.E →ₐ[ℚ] Qb) : ∃ σ : H.E ≃ₐ[ℚ] H.E, ∀ x, j' x = j (σ x) := by
  have := H.galois
  have inj : Function.Injective (fun σ : H.E ≃ₐ[ℚ] H.E => j.comp (σ : H.E →ₐ[ℚ] H.E)) := by
    intro σ τ hst
    exact AlgEquiv.ext fun x => j.toRingHom.injective (DFunLike.congr_fun hst x)
  have hb := (Fintype.bijective_iff_injective_and_card _).mpr ⟨inj, by
    rw [AlgHom.card, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]⟩
  obtain ⟨σ, hσ⟩ := hb.2 j'
  exact ⟨σ, fun x => (DFunLike.congr_fun hσ x).symm⟩

theorem range_eq (j : H.E →ₐ[ℚ] Qb) : j.fieldRange = H.EQ := by
  refine le_antisymm (le_iSup (fun j : H.E →ₐ[ℚ] Qb => j.fieldRange) j) (iSup_le fun j' => ?_)
  obtain ⟨σ, hσ⟩ := H.exists_aut j j'
  rintro _ ⟨x, rfl⟩
  exact ⟨σ x, (hσ x).symm⟩

theorem map_K (j : H.E →ₐ[ℚ] Qb) : H.K.map j = KQ H.d := by
  have hb : j H.sqd ^ 2 = ((-(H.d : ℤ) : ℤ) : Qb) := by rw [← map_pow, H.sqd_sq]; simp
  rw [K, adjoin_map, Set.image_singleton, KQ, sqQ_eq hb]

theorem FQ_le_EQ : H.FQ ≤ H.EQ := iSup_le fun j => by
  rintro _ ⟨x, -, rfl⟩
  exact H.mem_EQ j x

theorem KQ_le_EQ : KQ H.d ≤ H.EQ := by
  obtain ⟨j⟩ := H.nonempty_emb
  rw [← H.map_K j]
  rintro _ ⟨x, -, rfl⟩
  exact H.mem_EQ j x

def jOf (j : H.E →ₐ[ℚ] Qb) : H.E ≃ₐ[ℚ] H.EQ :=
  AlgEquiv.ofBijective (j.codRestrict H.EQ.toSubalgebra (H.mem_EQ j))
    ⟨fun x y hxy => j.toRingHom.injective (congrArg Subtype.val hxy), fun y => by
      have hy : (y : Qb) ∈ j.fieldRange := by rw [H.range_eq j]; exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩

instance fin_EQ : FiniteDimensional ℚ H.EQ := by
  obtain ⟨j⟩ := H.nonempty_emb
  exact (H.jOf j).toLinearEquiv.finiteDimensional

instance normal_EQ : Normal ℚ H.EQ := by
  obtain ⟨j⟩ := H.nonempty_emb
  have := H.galois
  exact Normal.of_algEquiv (H.jOf j)

instance fin_FQ : FiniteDimensional ℚ H.FQ :=
  FiniteDimensional.of_injective (inclusion H.FQ_le_EQ).toLinearMap (inclusion H.FQ_le_EQ).toRingHom.injective

variable {H}

variable (H)

end Formalism.HC.HostRaw

end
