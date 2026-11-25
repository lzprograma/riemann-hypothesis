module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsNhdsInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealDictionaryHypotheses

@[expose] public section

noncomputable section

namespace PositivityTheory.KCo

open Filter Topology NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.Ar.RT.Move

theorem indicator_mem {X : Type} [TopologicalSpace X] {U : Set X} (hU : IsClopen U) {Φ : X → ℂ} (h : Φ ∈ SB X) :
    U.indicator Φ ∈ SB X := by
  classical
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2.mono (fun x hx => ?_)⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ U
    · filter_upwards [hU.isOpen.mem_nhds hx, h1.eventually_eq x] with y hy hy'
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hy']
    · filter_upwards [hU.compl.isOpen.mem_nhds hx] with y hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · by_cases hxU : x ∈ U
    · simpa [Function.mem_support, hxU] using hx
    · simp [Function.mem_support, hxU] at hx

theorem kill {X : Type} [TopologicalSpace X] (N : Submodule ℂ (X → ℂ)) (Y₁ : X)
    (h : ∀ Y ≠ Y₁, ∃ m : X → ℂ, IsLocallyConstant m ∧ m Y ≠ m Y₁ ∧ ∀ Φ ∈ SB X, (fun y => (m y - m Y₁) * Φ y) ∈ N) :
    ∀ Φ ∈ SB X, Φ Y₁ = 0 → Φ ∈ N := by
  classical
  intro Φ hΦ hΦ0
  let mm : X → X → ℂ := fun Y => if hY : Y = Y₁ then 0 else Classical.choose (h Y hY)
  have hmm : ∀ Y, Y ≠ Y₁ → IsLocallyConstant (mm Y) ∧ mm Y Y ≠ mm Y Y₁ ∧
      ∀ Φ ∈ SB X, (fun y => (mm Y y - mm Y Y₁) * Φ y) ∈ N := by
    intro Y hY
    simp only [mm, dite_eq_right hY]
    exact Classical.choose_spec (h Y hY)
  let U : X → Set X := fun Y => {y | mm Y y ≠ mm Y Y₁}
  have hUc : ∀ Y, Y ≠ Y₁ → IsClopen (U Y) := by
    intro Y hY
    exact ((hmm Y hY).1.isClopen_fiber (mm Y Y₁)).compl
  have key : ∀ (s : Finset X), (∀ Y ∈ s, Y ≠ Y₁) → ∀ Ψ ∈ SB X,
      Function.support Ψ ⊆ ⋃ Y ∈ s, U Y → Ψ ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ Ψ _ hs
      have h0 : Ψ = 0 := by
        ext x
        by_contra hx
        have := hs hx
        simp at this
      rw [h0]
      exact N.zero_mem
    | insert Y s hYs ih =>
      intro hne Ψ hΨ hs
      have hY : Y ≠ Y₁ := hne Y (Finset.mem_insert_self _ _)
      have hsplit : Ψ = (U Y).indicator Ψ + (U Y)ᶜ.indicator Ψ :=
        (Set.indicator_self_add_compl _ _).symm
      rw [hsplit]
      refine N.add_mem ?_ ?_
      · obtain ⟨hlc, _, hN⟩ := hmm Y hY
        have hg : IsLocallyConstant (fun y => (mm Y y - mm Y Y₁)⁻¹) :=
          hlc.comp (fun a => (a - mm Y Y₁)⁻¹)
        have hΨg : (Ψ * fun y => (mm Y y - mm Y Y₁)⁻¹) ∈ SB X := ⟨hΨ.1.mul hg, hΨ.2.mul_right⟩
        have hI := hN _ (indicator_mem (hUc Y hY) hΨg)
        convert hI using 1
        ext y
        by_cases hy : y ∈ U Y
        · have hy' : mm Y y - mm Y Y₁ ≠ 0 := sub_ne_zero.mpr hy
          rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
          simp only [Pi.mul_apply]
          field_simp
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
      · refine ih (fun Z hZ => hne Z (Finset.mem_insert_of_mem hZ)) _
          (indicator_mem (hUc Y hY).compl hΨ) ?_
        intro x hx
        rw [Set.support_indicator] at hx
        obtain ⟨hx1, hx2⟩ := hx
        have := hs hx2
        simp only [Set.mem_iUnion, Finset.mem_insert, exists_prop] at this ⊢
        obtain ⟨Z, hZ, hxZ⟩ := this
        rcases hZ with rfl | hZ
        · exact absurd hxZ hx1
        · exact ⟨Z, hZ, hxZ⟩
  have hcl : IsClosed (Function.support Φ) := (hΦ.1.isClopen_fiber 0).isOpen.isClosed_compl
  have hS : IsCompact (Function.support Φ) := hΦ.2.isCompact.of_isClosed_subset hcl (subset_tsupport Φ)
  have hne : ∀ x ∈ Function.support Φ, x ≠ Y₁ := by
    rintro x hx rfl
    exact hx hΦ0
  have hnhds : ∀ x ∈ Function.support Φ, U x ∈ 𝓝 x := fun x hx =>
    (hUc x (hne x hx)).isOpen.mem_nhds (hmm x (hne x hx)).2.1
  obtain ⟨t, ht, hcov⟩ := hS.elim_nhds_subcover U hnhds
  exact key t (fun Y hY => hne Y (ht Y hY)) Φ hΦ hcov

theorem lc_of_mul {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] (m : X → ℂ)
    (h : ∀ Φ ∈ SB X, (fun y => m y * Φ y) ∈ SB X) : IsLocallyConstant m := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨V, hVc, hxV, hVK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hKx
  have hVc' : IsClopen V := hVc
  have hVcomp : IsCompact V := hK.of_isClosed_subset hVc'.1 hVK
  have hΦ : V.indicator (1 : X → ℂ) ∈ SB X := by
    refine ⟨?_, HasCompactSupport.intro hVcomp (fun y hy => Set.indicator_of_notMem hy _)⟩
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    by_cases hz : z ∈ V
    · filter_upwards [hVc'.isOpen.mem_nhds hz] with y hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem hz]
    · filter_upwards [hVc'.compl.isOpen.mem_nhds hz] with y hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hz]
  have hm := (h _ hΦ).1.eventually_eq x
  filter_upwards [hm, hVc'.isOpen.mem_nhds hxV] with y hy hyV
  simpa [Set.indicator_of_mem hyV, Set.indicator_of_mem hxV] using hy

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def ballAt (M : ℕ) (c : κ → Af F) (v : Pl F) : Set (κ → Fv F v) :=
  {z | ∀ i, Valued.v (z i - evalV F v (c i)) ≤ v.intValuation (M : 𝓞 F)}

private theorem coord_lemma {M : ℕ} (hM : M ≠ 0) (v : Pl F) (a : Fv F v) :
    IsClopen {z : Fv F v | Valued.v (z - a) ≤ v.intValuation (M : 𝓞 F)} ∧
      IsCompact {z : Fv F v | Valued.v (z - a) ≤ v.intValuation (M : 𝓞 F)} := by
  set π : Fv F v := ((M : 𝓞 F) : Fv F v) with hπ
  have hv : Valued.v π = v.intValuation (M : 𝓞 F) := by
    rw [hπ, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  have hM' : (M : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hv0 : Valued.v π ≠ 0 := hv ▸ IsDedekindDomain.HeightOneSpectrum.intValuation_ne_zero v _ hM'
  have hπ0 : π ≠ 0 := fun h => hv0 (by rw [h, map_zero])
  have hS : {z : Fv F v | Valued.v (z - a) ≤ v.intValuation (M : 𝓞 F)} =
      (fun z => (z - a) * π⁻¹) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, ← hv]
    rw [mul_inv_le_iff₀ (zero_lt_iff.mpr hv0), one_mul]
  have hO : IsClopen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isClopen_valuationSubring _
  have hcont : Continuous (fun z : Fv F v => (z - a) * π⁻¹) :=
    (continuous_id.sub continuous_const).mul continuous_const
  refine ⟨?_, ?_⟩
  · rw [hS]
    exact hO.preimage hcont
  · have himg : {z : Fv F v | Valued.v (z - a) ≤ v.intValuation (M : 𝓞 F)} =
        (fun y => a + π * y) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
      rw [hS]
      ext z
      constructor
      · intro hz
        refine ⟨(z - a) * π⁻¹, hz, ?_⟩
        field_simp
        ring
      · rintro ⟨y, hy, rfl⟩
        have : (a + π * y - a) * π⁻¹ = y := by field_simp; ring
        show (a + π * y - a) * π⁻¹ ∈ (v.adicCompletionIntegers F : Set (Fv F v))
        rw [this]
        exact hy
    rw [himg]
    have hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
      have := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
      exact isCompact_iff_compactSpace.mpr this
    exact hc.image (continuous_const.add (continuous_const.mul continuous_id))

theorem ball_mem {M : ℕ} (hM : M ≠ 0) (c : κ → Af F) (v : Pl F) : (ballAt M c v).indicator (1 : (κ → Fv F v) → ℂ) ∈ SB (κ → Fv F v) := by
  classical
  have hI : ballAt M c v = ⋂ i, (fun z : κ → Fv F v => z i) ⁻¹'
      {z : Fv F v | Valued.v (z - evalV F v (c i)) ≤ v.intValuation (M : 𝓞 F)} := by
    ext z
    simp [ballAt]
  have hP : ballAt M c v = Set.pi Set.univ (fun i =>
      {z : Fv F v | Valued.v (z - evalV F v (c i)) ≤ v.intValuation (M : 𝓞 F)}) := by
    ext z
    simp [ballAt]
  have hcl : IsClopen (ballAt M c v) := by
    rw [hI]
    exact isClopen_iInter_of_finite (fun i => (coord_lemma hM v _).1.preimage (continuous_apply i))
  have hco : IsCompact (ballAt M c v) := by
    rw [hP]
    exact isCompact_univ_pi (fun i => (coord_lemma hM v _).2)
  refine ⟨?_, HasCompactSupport.intro hco (fun x hx => Set.indicator_of_notMem hx _)⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ ballAt M c v
  · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem ball_cof {M : ℕ} (hM : M ≠ 0) (c : κ → Af F) :
    ∀ᶠ v in cofinite, (ballAt M c v).indicator (1 : (κ → Fv F v) → ℂ) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  classical
  have h1 : ∀ᶠ v in cofinite, (v : Pl F).intValuation (M : 𝓞 F) = 1 := by
    have hM' : (M : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hM
    have hI : Ideal.span {(M : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hM'
    rw [Filter.eventually_cofinite]
    refine (Ideal.finite_factors hI).subset (fun v hv => ?_)
    simp only [Set.mem_setOf_eq, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff, not_not] at hv
    rw [Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hv
  have h2 : ∀ᶠ v in cofinite, ∀ i, evalV F v (c i) ∈ (v : Pl F).adicCompletionIntegers F := by
    rw [Filter.eventually_all]
    intro i
    exact (c i).2
  filter_upwards [h1, h2] with v hv1 hv2
  have hset : ballAt M c v = {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
    ext z
    simp only [ballAt, Set.mem_setOf_eq, hv1]
    refine forall_congr' (fun i => ?_)
    have hc := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hv2 i)
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    constructor
    · intro h
      have e : z i = (z i - evalV F v (c i)) + evalV F v (c i) := by ring
      rw [e]
      exact le_trans (Valuation.map_add _ _ _) (max_le h hc)
    · intro h
      exact le_trans (Valuation.map_sub _ _ _) (max_le h hc)
  rw [hset]

def box (M : ℕ) (c : κ → Af F) (y : κ → Af F) : ℂ := ∏ᶠ v, (ballAt M c v).indicator (1 : (κ → Fv F v) → ℂ) fun i => evalV F v (y i)

def Near (M : ℕ) (c y : κ → Af F) : Prop := ∀ v i, Valued.v (evalV F v (y i) - evalV F v (c i)) ≤ v.intValuation (M : 𝓞 F)

theorem box_of_near {M : ℕ} {c y : κ → Af F} (h : Near M c y) : box M c y = 1 :=
  finprod_eq_one_of_forall_eq_one fun v => Set.indicator_of_mem (show _ ∈ ballAt M c v from h v) _

theorem box_of_not {M : ℕ} (hM : M ≠ 0) {c y : κ → Af F} (h : ¬ Near M c y) : box M c y = 0 := by
  unfold Near at h
  push Not at h
  obtain ⟨v, i, hvi⟩ := h
  unfold box
  apply finprod_eq_zero _ v
  · apply Set.indicator_of_notMem
    intro hm
    exact absurd (hm i) (not_le.mpr hvi)
  · have hcof := ball_cof hM c
    have hy : ∀ᶠ w in cofinite, ∀ j, evalV F w (y j) ∈ (w : Pl F).adicCompletionIntegers F := by
      rw [Filter.eventually_all]
      intro j
      exact (y j).2
    have hev : ∀ᶠ w in cofinite,
        (ballAt M c w).indicator (1 : (κ → Fv F w) → ℂ) (fun j => evalV F w (y j)) = 1 := by
      filter_upwards [hcof, hy] with w hw hwy
      rw [hw]
      exact Set.indicator_of_mem (show (fun j => evalV F w (y j)) ∈ {x : κ → Fv F w | ∀ j, x j ∈ w.adicCompletionIntegers F} from hwy) _
    rw [Filter.eventually_cofinite] at hev
    exact hev

theorem Near.symm {M : ℕ} {c y : κ → Af F} (h : Near M c y) : Near M y c := by
  intro v i
  have := h v i
  rwa [← Valuation.map_neg, neg_sub] at this

theorem Near.trans {M : ℕ} {a b c : κ → Af F} (h : Near M a b) (h' : Near M b c) : Near M a c := by
  intro v i
  have h1 := h v i
  have h2 := h' v i
  have : evalV F v (c i) - evalV F v (a i) = (evalV F v (c i) - evalV F v (b i)) + (evalV F v (b i) - evalV F v (a i)) := by ring
  rw [this]
  exact le_trans (Valuation.map_add _ _ _) (max_le h2 h1)

theorem schA_le (L : Submodule ℂ ((κ → AF F) → ℂ))
    (hL : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ L) :
    schA F κ ≤ L :=
  by apply _root_.GlobalTheory.ThetaInterchange.schA_le_of_pure <;> assumption

end PositivityTheory.KCo
