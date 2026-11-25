module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagValuationNormalization
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.StepRowsInverseNonzeroEntry
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValuationRingExtensionSpecialization
import Mathlib.Tactic.Linter.Style

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Fwd

open GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Lift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem val_lift_of {Ω Φ : Type} [Field Ω] [Field Φ] (φ : Ω →+* Φ) {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}
    (hb : IsBlockMap κ v) {x : (Σ k, ι k) → Ω} {y : (Σ k, ι' k) → Φ} (hy : y ∘ v = φ ∘ x)
    {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {s : Ω} (hs : RegAt x (mCoordIdeal (z ∘ v)) s) :
    IsValueAt y (φ s) z (valAt x s (z ∘ v)) := by
  have hzb := comp_mem_mcPts hb φ hy hz
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have hg' := isMultiHomog_rename_block hb hg
  have hh' := isMultiHomog_rename_block hb hh
  have hn' : rename v h ∉ mCoordIdeal z := rename_notMem hb hn
  have heq' : aeval y (rename v g) = φ s * aeval y (rename v h) := by
    rw [aeval_rename, aeval_rename, hy, aeval_comp_ringHom, aeval_comp_ringHom, heq, map_mul]
  have v1 : IsValueAt x s (z ∘ v) _ :=
    ⟨d, g, h, hg, hh, aeval_ne_zero_of_notMem hzb hh hn, heq, eval_ne_zero_of_notMem hh hn, rfl⟩
  have v2 : IsValueAt y (φ s) z _ :=
    ⟨_, _, _, hg', hh', aeval_ne_zero_of_notMem hz hh' hn', heq', eval_ne_zero_of_notMem hh' hn', rfl⟩
  rw [valAt_eq hzb v1]
  rw [eval_rename_block, eval_rename_block] at v2
  exact v2

end Lift

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem exists_section (M : FlagModel y Ψ N j) {κ : Kk → K} {v : (Σ k, ιk k) → Σ k, ι k} (hb : IsBlockMap κ v)
    (hr : ∀ k, (∀ p, M.blk p ≠ some k) → k ∈ Set.range κ) :
    ∃ (κ' : NonPluckerBlocks M.blk → Kk) (v' : (Σ k, baseIdx ι M.blk k) → Σ k, ιk k), IsBlockMap κ' v' ∧
      ∀ q, v (v' q) = ⟨q.1.1, q.2⟩ := by
  choose κ' hκ' using fun k : NonPluckerBlocks M.blk => hr k.1 k.2
  have hq : ∀ q : Σ k, baseIdx ι M.blk k, ∃ p, v p = ⟨q.1.1, q.2⟩ := fun q =>
    hb.2.2.2 ⟨q.1.1, q.2⟩ ⟨κ' q.1, hκ' q.1⟩
  choose v' hv' using hq
  refine ⟨κ', v', ⟨fun a b h => Subtype.ext (by rw [← hκ' a, ← hκ' b, h]), fun a b h => ?_, fun q => ?_, ?_⟩, hv'⟩
  · have h' := congrArg v h
    rw [hv', hv'] at h'
    exact (blockMap_base M).2.1 h'
  · refine hb.1 ?_
    rw [hκ', ← hb.2.2.1, hv']
  · rintro ⟨k, i⟩ ⟨⟨kb, hkb⟩, rfl⟩
    rcases hvq : v ⟨κ' ⟨kb, hkb⟩, i⟩ with ⟨k₂, i₂⟩
    have hk₂ : k₂ = kb := by
      have h1 := hb.2.2.1 ⟨κ' ⟨kb, hkb⟩, i⟩
      rw [hvq] at h1
      exact h1.trans (hκ' ⟨kb, hkb⟩)
    subst hk₂
    refine ⟨⟨⟨k₂, hkb⟩, i₂⟩, hb.2.1 ?_⟩
    rw [hv', hvq]

theorem exists_pre {κ : Kk → K} {v : (Σ k, ιk k) → Σ k, ι k} (hb : IsBlockMap κ v) (k₁ : Kk) (m : ι (κ k₁)) :
    ∃ i : ιk k₁, v ⟨k₁, i⟩ = ⟨κ k₁, m⟩ := by
  obtain ⟨⟨k₂, i⟩, hp⟩ := hb.2.2.2 ⟨κ k₁, m⟩ ⟨k₁, rfl⟩
  have hk : k₂ = k₁ := hb.1 (by simpa [hp] using (hb.2.2.1 ⟨k₂, i⟩).symm)
  subst hk
  exact ⟨i, hp⟩

theorem ratio_up {κ : Kk → K} {v : (Σ k, ιk k) → Σ k, ι k} (hb : IsBlockMap κ v) {z : (Σ k, ιk k) → ℂ} {k₁ : Kk}
    {m c : ι (κ k₁)} (hy : y ⟨κ k₁, c⟩ ≠ 0) (hz : upV v z ⟨κ k₁, c⟩ ≠ 0) :
    IsValueAt (y ∘ v) (y ⟨κ k₁, m⟩ / y ⟨κ k₁, c⟩) z (upV v z ⟨κ k₁, m⟩ / upV v z ⟨κ k₁, c⟩) := by
  obtain ⟨im, hm⟩ := exists_pre hb k₁ m
  obtain ⟨ic, hc⟩ := exists_pre hb k₁ c
  rw [← hc] at hy hz ⊢
  rw [← hm]
  rw [upV_apply hb.2.1] at hz ⊢
  rw [upV_apply hb.2.1]
  exact isValueAt_ratio (y := y ∘ v) hy hz

theorem exists_coord {κ : Kk → K} {v : (Σ k, ιk k) → Σ k, ι k} (hb : IsBlockMap κ v) {z : (Σ k, ιk k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (y ∘ v))) (k₁ : Kk) :
    ∃ c : ι (κ k₁), upV v z ⟨κ k₁, c⟩ ≠ 0 ∧ y ⟨κ k₁, c⟩ ≠ 0 := by
  obtain ⟨c₁, hc₁⟩ := hz.1 k₁
  have hy : (y ∘ v) ⟨k₁, c₁⟩ ≠ 0 := coord_ne hz hc₁
  have hex : ∃ c : ι (κ k₁), v ⟨k₁, c₁⟩ = ⟨κ k₁, c⟩ := by
    rcases hq : v ⟨k₁, c₁⟩ with ⟨kq, c⟩
    have h1 : kq = κ k₁ := by
      have h2 := hb.2.2.1 ⟨k₁, c₁⟩
      rw [hq] at h2
      exact h2
    subst h1
    exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, ?_, ?_⟩
  · rw [← hc, upV_apply hb.2.1]
    exact hc₁
  · rw [← hc]
    exact hy

theorem flag_fwd_kept (M : FlagModel y Ψ N j) (keep : Ψ × Fin N → Prop) {κ : Kk → K} {v : (Σ k, ιk k) → Σ k, ι k}
    (hb : IsBlockMap κ v)
    (hrange : ∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k))
    {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {z : (Σ k, ιk k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (y ∘ v))) (hG : M.GoodAt F (mCoordIdeal (pBase M v z))) :
    ∃ H : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (H τ) ∧ (H τ).det ≠ 0) ∧
      ∀ p k, keep p → M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k,
        upV v z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (pBase M v z) * minorIJ (H p.1) I (stepCols N j p.2) := by
  obtain ⟨κ', v', hb', hv'⟩ := exists_section M hb fun k h => (hrange k).2 (Or.inl h)
  let am := algebraMap M.Ω Φ
  have hx : (y ∘ v) ∘ v' = am ∘ M.x := funext fun q => by
    show y (v (v' q)) = am (M.x q)
    rw [hv']
    exact M.y_base q
  have hpb : pBase M v z = z ∘ v' := funext fun q => by
    show upV v z ⟨q.1.1, q.2⟩ = z (v' q)
    rw [← hv' q, upV_apply hb.2.1]
  rw [hpb] at hG ⊢
  have hzb : z ∘ v' ∈ mcPts (mCoordIdeal M.x) := comp_mem_mcPts hb' am hx hz
  exact flag_fwd_core M hF hzb hG (regRing (y ∘ v) z) (regVal hz) (regVal_local hz)
    (fun hs => ⟨_, val_lift_of am hb' hx hz hs⟩) (fun hs => regVal_eq hz _ (val_lift_of am hb' hx hz hs))
    keep (upV v z) (fun p k hkp hp => by
      obtain ⟨k₁, rfl⟩ := (hrange k).2 (Or.inr ⟨p, hkp, hp⟩)
      obtain ⟨c, hzc, hyc⟩ := exists_coord hb hz k₁
      exact ⟨c, hzc, hyc, fun m => ⟨⟨_, ratio_up hb hyc hzc⟩, regVal_eq hz _ (ratio_up hb hyc hzc)⟩⟩)

end Flag

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ιk k) → ℂ), M.IsFrame F → z ∈ mcPts (mCoordIdeal (y ∘ v)) → M.GoodAt F (mCoordIdeal (pBase M v z)) → (∀ k, pBase M v z ⟨k, F.c k⟩ = 1) → ∃ H : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (H τ) ∧ (H τ).det ≠ 0) ∧ ∀ p k, keep p → M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, upV v z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (pBase M v z) * minorIJ (H p.1) I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M keep Kk _ ιk _ κ v hb hrange F z hF hz hG _
  exact flag_fwd_kept M keep hb hrange hF hz hG

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Fwd
