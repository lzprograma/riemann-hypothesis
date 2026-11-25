module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Pt

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}

theorem mConeMap_rename {Ω : Type} [Field Ω] (hv : IsBlockMap κ v) (y : (Σ k, ι' k) → Ω) (g : MRing ι) :
    mConeMap y (rename v g) = rename κ (mConeMap (y ∘ v) g) :=
  _root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.mConeMap_rename hv y g

theorem rename_mem_iff {Ω : Type} [Field Ω] (hv : IsBlockMap κ v) (y : (Σ k, ι' k) → Ω) (g : MRing ι) :
    rename v g ∈ mCoordIdeal y ↔ g ∈ mCoordIdeal (y ∘ v) := by
  change mConeMap y (rename v g) = 0 ↔ mConeMap (y ∘ v) g = 0
  rw [mConeMap_rename hv]
  exact map_eq_zero_iff _ (rename_injective κ hv.1)

theorem mCoordIdeal_comp {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) :
    mCoordIdeal (φ ∘ x) = mCoordIdeal x := by
  ext g
  change mConeMap (φ ∘ x) g = 0 ↔ mConeMap x g = 0
  rw [_root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.mConeMap_comp]
  exact map_eq_zero_iff _ (map_injective φ φ.injective)

theorem eval_rename_eq (z : (Σ k, ι' k) → ℂ) (g : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename v g)) = eval (z ∘ v) (map (Int.castRingHom ℂ) g) := by
  rw [map_rename, eval_rename]

theorem sum_mapDomain_block (hv : ∀ p, (v p).1 = κ p.1) [DecidableEq K'] (m : (Σ k, ι k) →₀ ℕ) (k' : K') :
    ∑ i, (Finsupp.mapDomain v m) ⟨k', i⟩ = ∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0 := by
  convert _root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.sum_mapDomain_block hv m k'

theorem isMultiHomog_rename_block (hb : IsBlockMap κ v) {f : MRing ι} {b : K → ℕ} (hf : IsMultiHomog f b) :
    IsMultiHomog (rename v f) (Function.extend κ b 0) :=
  _root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.isMultiHomog_rename_block hb hf

theorem comp_mem_mcPts {Ω Ω' : Type} [Field Ω] [Field Ω'] (hv : IsBlockMap κ v)
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q))
    {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x')) : z ∘ v ∈ mcPts (mCoordIdeal x) :=
  _root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.comp_mem_mcPts hv φ (funext hx) hz

theorem aeval_rename_pull {Ω Ω' : Type} [Field Ω] [Field Ω'] {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'}
    (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q)) (f : MRing ι) :
    aeval x' (rename v f) = φ (aeval x f) := by
  rw [aeval_rename, show x' ∘ v = φ ∘ x from funext hx, aeval_def, aeval_def, algebraMap_int_eq,
    algebraMap_int_eq, eval₂_comp_left φ, RingHom.ext_int (φ.comp (Int.castRingHom Ω)) (Int.castRingHom Ω')]

theorem regAt_pull {Ω Ω' : Type} [Field Ω] [Field Ω'] (hv : IsBlockMap κ v)
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q))
    {z : (Σ k, ι' k) → ℂ} {s : Ω} (hs : RegAt x (mCoordIdeal (z ∘ v)) s) :
    RegAt x' (mCoordIdeal z) (φ s) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  refine ⟨_, rename v g, rename v h, isMultiHomog_rename_block hv hg, isMultiHomog_rename_block hv hh,
    fun hm => hn ((rename_mem_iff hv z h).1 hm), ?_⟩
  rw [aeval_rename_pull φ hx, aeval_rename_pull φ hx, heq, map_mul]

theorem isValueAt_pull {Ω Ω' : Type} [Field Ω] [Field Ω'] (hv : IsBlockMap κ v)
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q))
    {z : (Σ k, ι' k) → ℂ} {s : Ω} {w : ℂ} (hs : IsValueAt x s (z ∘ v) w) : IsValueAt x' (φ s) z w := by
  obtain ⟨d, g, h, hg, hh, hy, heq, h0, rfl⟩ := hs
  have hpull := aeval_rename_pull (v := v) φ hx
  refine ⟨_, rename v g, rename v h, isMultiHomog_rename_block hv hg, isMultiHomog_rename_block hv hh, ?_, ?_, ?_, ?_⟩
  · rw [hpull]; exact (map_ne_zero φ).2 hy
  · rw [hpull, hpull, heq, map_mul]
  · rwa [eval_rename_eq]
  · rw [eval_rename_eq, eval_rename_eq]

end General

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ), zb ∈ mcPts (mCoordIdeal M'.x) → zb ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) ∧ ∀ s : M.Ω, RegAt M.x (mCoordIdeal (zb ∘ Cv.v)) s → RegAt M'.x (mCoordIdeal zb) (Cv.φ s) ∧ valAt M'.x (Cv.φ s) zb = valAt M.x s (zb ∘ Cv.v) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb hzb
  have hz := comp_mem_mcPts Cv.block Cv.φ Cv.x_eq hzb
  refine ⟨hz, fun s hs => ?_⟩
  obtain ⟨w, hw⟩ := ValRing.exists_isValueAt hz hs
  have hw' := isValueAt_pull Cv.block Cv.φ Cv.x_eq hw
  exact ⟨regAt_pull Cv.block Cv.φ Cv.x_eq hs, by rw [valAt_eq hzb hw', valAt_eq hz hw]⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Pt
