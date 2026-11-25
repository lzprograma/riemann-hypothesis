module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedOfIsIntegral
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLBoundedEntriesCompletionFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsCompactClosureZpowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFiniteness
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerLocalUnitaryCommOfSeparable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
import Mathlib.Tactic.Linter.Style

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.LocGoodProof

section Generic

variable {G G' : Type} [Group G] [Group G']

theorem mem_twCent_prodMap (θ : G →* G) (θ' : G' →* G') (δ g : G × G') :
    g ∈ twCent (θ.prodMap θ') δ ↔ g.1 ∈ twCent θ δ.1 ∧ g.2 ∈ twCent θ' δ.2 := by
  change g * δ = δ * (θ.prodMap θ') g ↔ g.1 * δ.1 = δ.1 * θ g.1 ∧ g.2 * δ.2 = δ.2 * θ' g.2
  exact Prod.ext_iff

variable [TopologicalSpace G] [TopologicalSpace G']

theorem isCompact_closure_zpowers_of_map [T2Space G'] (φ : G →* G') (hφ : Continuous φ) (t : G)
    (ht : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (φ t) : Set G')) := by
  have hC := ht.image hφ
  refine hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed)
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

theorem cptPart_le_prod [T2Space G] [T2Space G'] [ContinuousMul G] [ContinuousMul G'] (S : Subgroup (G × G'))
    (T : Subgroup G) (T' : Subgroup G') (hS : ∀ g ∈ S, g.1 ∈ T ∧ g.2 ∈ T') :
    cptPart S ≤ (cptPart T).prod (cptPart T') := by
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨htS, htc⟩
  exact ⟨Subgroup.subset_closure ⟨(hS t htS).1,
      isCompact_closure_zpowers_of_map (MonoidHom.fst G G') continuous_fst t htc⟩,
    Subgroup.subset_closure ⟨(hS t htS).2,
      isCompact_closure_zpowers_of_map (MonoidHom.snd G G') continuous_snd t htc⟩⟩

theorem good_prod {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G)
    (K' : Subgroup G') (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) (ho' : IsOpen (K' : Set G'))
    (hc' : IsCompact (K' : Set G')) (δ : G × G')
    (hcomm : ∀ a b, a ∈ twCent θ δ.1 → b ∈ twCent θ δ.1 → a * b = b * a)
    (hcomm' : ∀ a b, a ∈ twCent θ' δ.2 → b ∈ twCent θ' δ.2 → a * b = b * a)
    (H : Subgroup G) (H' : Subgroup G') (hH : IsCompact (H : Set G)) (hH' : IsCompact (H' : Set G'))
    (hP : cptPart (twCent θ δ.1) ≤ H) (hP' : cptPart (twCent θ' δ.2) ≤ H') :
    PositivityTheory.Rg.BcB.G8.Fin.Good (θ.prodMap θ') (K.prod K') δ := by
  have hmem := fun g => mem_twCent_prodMap θ θ' δ g
  have hKo : IsOpen ((K.prod K' : Subgroup (G × G')) : Set (G × G')) := by
    rw [Subgroup.coe_prod]; exact ho.prod ho'
  have hKc : IsCompact ((K.prod K' : Subgroup (G × G')) : Set (G × G')) := by
    rw [Subgroup.coe_prod]; exact hc.prod hc'
  have hHc : IsCompact ((H.prod H' : Subgroup (G × G')) : Set (G × G')) := by
    rw [Subgroup.coe_prod]; exact hH.prod hH'
  have hle : cptPart (twCent (θ.prodMap θ') δ) ≤ H.prod H' :=
    (cptPart_le_prod _ _ _ fun g hg => (hmem g).1 hg).trans (Subgroup.prod_mono hP hP')
  refine ⟨fun g hg g' hg' => ?_, fun x => ⟨GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj _ hKc x),
    GlobalTheory.LocFin.relIndex_cptPart_ne_zero _ _ _ (GlobalTheory.LocFin.isOpen_map_conj _ hKo x) hHc hle⟩⟩
  obtain ⟨ga, gb⟩ := (hmem g).1 hg
  obtain ⟨ga', gb'⟩ := (hmem g').1 hg'
  exact Prod.ext (hcomm _ _ ga ga') (hcomm' _ _ gb gb')

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mul_nrmL_comm (hU : Unr E) (n : ℕ) (w : Pl E) {y g : GLw n w} (hg : g ∈ twCent (thL n w) y) :
    g * nrmL n w y = nrmL n w y * g :=
  (GlobalTheory.CptTorus.twCent_commute hU n w y hg).eq

theorem twCent_comm (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hy : (nrmL n w y).val.charpoly.Separable)
    (g h : GLw n w) (hg : g ∈ twCent (thL n w) y) (hh : h ∈ twCent (thL n w) y) : g * h = h * g := by
  have key : ∀ {u : GLw n w}, u ∈ twCent (thL n w) y → Commute (nrmL n w y).val u.val := fun {u} hu => by
    have := congrArg Units.val (mul_nrmL_comm hU n w hu)
    rw [Units.val_mul, Units.val_mul] at this
    exact this.symm
  exact Units.ext (GlobalTheory.BCT.CentComm.commute_of_commute_separable hy (key hg) (key hh)).eq

theorem cptPart_le_compact (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hs : (nrmL n w y).val.charpoly.Separable) :
    ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H :=
  GlobalTheory.CptTorus.main E hU n w y hs

theorem good_pair (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable) :
    PositivityTheory.Rg.BcB.G8.Fin.Good ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) y := by
  obtain ⟨ho₁, hc₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨ho₂, hc₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  obtain ⟨H₁, hH₁, hP₁⟩ := cptPart_le_compact hU a w y.1 h₁
  obtain ⟨H₂, hH₂, hP₂⟩ := cptPart_le_compact hU b w y.2 h₂
  exact good_prod (G := GLw a w) (G' := GLw b w) (thL a w) (thL b w) (GlobalTheory.LFun.KGL w (n := a)) (GlobalTheory.LFun.KGL w (n := b))
    ho₁ hc₁ ho₂ hc₂ y (twCent_comm hU a w y.1 h₁) (twCent_comm hU b w y.2 h₂) H₁ H₂ hH₁ hH₂ hP₁ hP₂

theorem locGood : PositivityTheory.Rg.BcB.G8.Fin.LocGood := by
  intro E _ _ _ hU a b w y h₁ h₂
  exact good_pair hU a b w y h₁ h₂

end GlobalTheory.CompanionTheory.LocGoodProof

end
