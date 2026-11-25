module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.HalfModCompact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nabs_pow_eq (y : kˣ) (n : ℕ) : nabs k (y ^ n) = nabs k y ^ n := by
  unfold nabs
  rw [map_pow, NNReal.coe_pow]

theorem nabs_inv_eq (y : kˣ) : nabs k y⁻¹ = (nabs k y)⁻¹ := by
  unfold nabs
  rw [map_inv, NNReal.coe_inv]

theorem nabs_eq_one_of_pow_le (y : kˣ) (B : ℝ) (h₁ : ∀ n : ℕ, nabs k (y ^ n) ≤ B)
    (h₂ : ∀ n : ℕ, nabs k (y⁻¹ ^ n) ≤ B) : nabs k y = 1 := by
  have hpos : 0 < nabs k y := (nabs_properties k).2.1 y
  rcases lt_trichotomy (nabs k y) 1 with hlt | heq | hgt
  · exfalso
    have hinv : 1 < (nabs k y)⁻¹ := (one_lt_inv₀ hpos).2 hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hinv
    have h3 := h₂ n
    rw [nabs_pow_eq, nabs_inv_eq] at h3
    linarith
  · exact heq
  · exfalso
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hgt
    have h3 := h₁ n
    rw [nabs_pow_eq] at h3
    linarith

def blockDet {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) (g : GL (Fin N) k) : k :=
  Matrix.det (Matrix.of fun i j : Fin (d a) =>
    (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩))

theorem continuous_blockDet {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) :
    Continuous (blockDet (k := k) d hd a) := by
  unfold blockDet
  first
    | fun_prop

theorem blockDet_leviEmb {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h)
    (x : Levi k (Bl d)) :
    blockDet d hd a (leviEmb k (stdBlocks d hd) x) =
      ((Matrix.GeneralLinearGroup.det (x a) : kˣ) : k) := by
  unfold blockDet
  have hm : (Matrix.of fun i j : Fin (d a) =>
      ((leviEmb k (stdBlocks d hd) x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
        (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩)) =
      ((x a : GL (Bl d a) k) : Matrix (Bl d a) (Bl d a) k) := by
    ext i j
    simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
  rw [hm, Matrix.GeneralLinearGroup.val_det_apply]

theorem nabs_det_eq_one_of_mem_KM {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    {J : Subgroup (GL (Fin N) k)} (hJ : IsCompact (J : Set (GL (Fin N) k)))
    {x : Levi k (Bl d)} (hx : x ∈ KM k N J d hd) (a : Fin h) :
    nabs k (Matrix.GeneralLinearGroup.det (x a)) = 1 := by
  have hmem : ∀ z ∈ KM k N J d hd, blockDet d hd a (leviEmb k (stdBlocks d hd) z) ∈
      blockDet (k := k) d hd a '' (J : Set (GL (Fin N) k)) :=
    fun z hz => ⟨_, hz, rfl⟩
  obtain ⟨B, hB⟩ := GlobalTheory.ZetaConvergence.exists_nabs_le (hJ.image (continuous_blockDet d hd a))
  apply nabs_eq_one_of_pow_le _ B
  · intro n
    apply hB
    have h1 := hmem _ ((KM k N J d hd).pow_mem hx n)
    have e : (x ^ n) a = x a ^ n := rfl
    rw [blockDet_leviEmb, e, map_pow] at h1
    exact h1
  · intro n
    apply hB
    have h1 := hmem _ ((KM k N J d hd).pow_mem ((KM k N J d hd).inv_mem hx) n)
    have e : (x⁻¹ ^ n) a = (x a)⁻¹ ^ n := rfl
    rw [blockDet_leviEmb, e, map_pow, map_inv] at h1
    exact h1

theorem deltaHalf_eq_one_of_mem_KM :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)),
      IsCompact (J : Set (GL (Fin N) k)) → ∀ x ∈ KM k N J d hd, deltaHalf k (Bl d) x = 1 := by
  intro k _ _ _ _ N h d hd J hJ x hx
  unfold deltaHalf
  rw [MonoidHom.finsetProd_apply]
  apply Finset.prod_eq_one
  intro a _
  rw [MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
  unfold detChar
  rw [MonoidHom.comp_apply]
  apply Units.ext
  simp [absPow, nabs_det_eq_one_of_mem_KM d hd hJ hx a]

end GlobalTheory.CompanionTheory.HalfModCompact
