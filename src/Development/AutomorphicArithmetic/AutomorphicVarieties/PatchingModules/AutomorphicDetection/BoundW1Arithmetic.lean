module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualEvalBidualApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArPresAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArPres
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.UnrLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.ArPl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.W1BoundArithmeticRankTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.OrdinaryHeckeAlgebraIntegral
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

noncomputable section

private theorem mod_one (l : ℕ) [Fact l.Prime] (j : ZMod l ≃+* ZMod (l ^ 1)) (x : ℤ_[l]) :
    j (PadicInt.toZMod x) = PadicInt.toZModPow 1 x := by
  have hx := PadicInt.sub_zmodRepr_mem x
  have h1 : PadicInt.toZMod (x - (PadicInt.zmodRepr x : ℤ_[l])) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod]; exact hx
  have h2 : PadicInt.toZModPow 1 (x - (PadicInt.zmodRepr x : ℤ_[l])) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p]; exact hx
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2]
  simp only [map_natCast]

private theorem dualPair_one_of_isDualPair {l : ℕ} [Fact l.Prime] {R Γ M M' : Type}
    [CommRing R] [Group Γ] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    {ε : Γ →* ℤ_[l]ˣ} {ρ : Representation R Γ M} {ρ' : Representation R Γ M'}
    {b : M →+ M' →+ ZMod l} (hb : IsDualPair ε ρ ρ' b) :
    UpperTheory.V.Th.DualPair 1 ε ρ ρ' (b.compr₂ (ZMod.ringEquivCongr (pow_one l).symm).toAddMonoidHom) := by
  let j : ZMod l ≃+* ZMod (l ^ 1) := ZMod.ringEquivCongr (pow_one l).symm
  refine ⟨fun x h => hb.left x fun y => j.injective ((h y).trans (map_zero j).symm),
    fun y h => hb.right y fun x => j.injective ((h x).trans (map_zero j).symm),
    fun g x y => ?_⟩
  change j (b (ρ g x) (ρ' g y)) = PadicInt.toZModPow 1 (ε g : ℤ_[l]) * j (b x y)
  rw [hb.equiv, map_mul, epsBar, mod_one l j]

theorem UpperTheory.V.Pa.gwBare :
    GreenbergWiles → LocalTateDuality → GlobalFiniteness → LocalFiniteness → ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (e : GS Ω S ≃ₜ* Γ) (ε : Γ →* ℤ_[l]ˣ) (W : Type) [Fintype W] (pl : W ≃ S) (A : W → ValuationSubring Ω) (D : W → Type) [∀ w, Group (D w)] [∀ w, TopologicalSpace (D w)] (ι : ∀ w, D w →* Γ) (α : ∀ w, D w ≃ₜ* Dec (F := F) (A w)) (d : ℕ) (ip : Fin d ≃ InfinitePlace F) (c : Fin d → G F Ω), l ≠ 2 → (∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) → (∀ g, ε (e (toGS Ω S g)) = cycZ F Ω l g) → (∀ w, IsPlaceOver (A w) (pl w).1) → (∀ w g, ι w g = e (toGS Ω S (α w g : G F Ω))) → (∀ i, IsCCAt (ip i) (c i)) → GWBare ε D ι fun i => e (toGS Ω S (c i)) :=
  fun hGW hT hGF hLF l _ F Ω _ _ _ _ _ _ S Γ _ _ _ e ε W _ pl A D _ _ ι α d ip c hl hS hε hA hι hc
    R M M' _ _ _ _ _ _ _ ρ ρ' _ hLC hb =>
    UpperTheory.V.Th.gwCntBare hGW hT hGF hLF l F Ω S Γ e ε W pl A D ι α d ip c hl hS hε hA hι hc
      1 one_pos R M M' ρ ρ' _ hLC (dualPair_one_of_isDualPair hb)

theorem UpperTheory.V.Pa.locBare :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → (((l : ℕ) : 𝓞 F) ∈ v.asIdeal → LocCount (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) (locDeg v)) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → LocCount (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) 0) := by
  intro hF hT hE l _ F Ω _ _ _ _ _ A v hv
  have ⟨h1, h2⟩ := UpperTheory.V.Th.locCntBare hF hT hE l F Ω A v hv
  exact ⟨fun hl R M M' _ _ _ _ _ _ _ ρ ρ' _ hLC hb => h1 hl 1 one_pos R M M' ρ ρ' _ hLC (dualPair_one_of_isDualPair hb),
    fun hl R M M' _ _ _ _ _ _ _ ρ ρ' _ hLC hb => h2 hl 1 one_pos R M M' ρ ρ' _ hLC (dualPair_one_of_isDualPair hb)⟩

theorem UpperTheory.V.Pa.locCongr :
    ∀ (l : ℕ) [Fact l.Prime] (D D' : Type) [Group D] [TopologicalSpace D] [Group D'] [TopologicalSpace D'] (α : D ≃ₜ* D') (ε : D →* ℤ_[l]ˣ) (ε' : D' →* ℤ_[l]ˣ) (d : ℕ), (∀ g, ε g = ε' (α g)) → LocCount D' ε' d → LocCount D ε d := by
  intro l _ D D' _ _ _ _ α ε ε' d hε h R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hdual
  let σ : D' →* D := α.symm.toMulEquiv.toMonoidHom
  have hσ : ∀ g, σ g = α.symm g := fun g => rfl
  let ρ2 : Representation R D' M := ρ.comp σ
  let ρ2' : Representation R D' M' := ρ'.comp σ
  have heps : ∀ g : D', epsBar ε (α.symm g) = epsBar ε' g := by
    intro g
    simp only [epsBar, hε, ContinuousMulEquiv.apply_symm_apply]
  have hLC2 : LC ρ2 := fun m => (hLC m).comp_continuous α.symm.continuous
  have hdual2 : IsDualPair ε' ρ2 ρ2' b := by
    refine ⟨hdual.left, hdual.right, fun g x y => ?_⟩
    have := hdual.equiv (α.symm g) x y
    rw [← heps g, ← this]
    rfl
  obtain ⟨hfin, hcard⟩ := h R M M' ρ2 ρ2' b hLC2 hdual2
  let e : Zl ρ ≃ Zl ρ2 :=
    { toFun := fun z => ⟨fun g => z.1 (α.symm g), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨hz1.comp_continuous α.symm.continuous, fun g k => ?_⟩
        show z.1 (α.symm (g * k)) = z.1 (α.symm g) + ρ (α.symm g) (z.1 (α.symm k))
        rw [map_mul]
        exact hz2 _ _⟩
      invFun := fun z => ⟨fun g => z.1 (α g), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨hz1.comp_continuous α.continuous, fun g k => ?_⟩
        have := hz2 (α g) (α k)
        rw [← map_mul] at this
        show z.1 (α (g * k)) = z.1 (α g) + ρ g (z.1 (α k))
        rw [this]
        show z.1 (α g) + ρ (α.symm (α g)) (z.1 (α k)) = _
        rw [ContinuousMulEquiv.symm_apply_apply]⟩
      left_inv := fun z => by
        apply Subtype.ext
        funext g
        show z.1 (α.symm (α g)) = z.1 g
        rw [ContinuousMulEquiv.symm_apply_apply]
      right_inv := fun z => by
        apply Subtype.ext
        funext g
        show z.1 (α (α.symm g)) = z.1 g
        rw [ContinuousMulEquiv.apply_symm_apply] }
  have hinv : Nat.card ρ2'.invariants = Nat.card ρ'.invariants := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun v => ?_)
    simp only [Representation.mem_invariants]
    constructor
    · intro hv g
      have := hv (α g)
      simpa [ρ2', hσ] using this
    · intro hv g
      exact hv (α.symm g)
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, hcard, hinv]

theorem UpperTheory.V.Pa.presCounts :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (Lc : Loc) (G : Glob l Lc) (q d : ℕ) (a : ArData G q d) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (_ : ArPres a F Ω), l ≠ 2 → (∀ u, UnrCount l (Lc.Gu u) (Lc.Ju u)) → a.Counts := by
  intro hC l _ Lc G q d a F Ω _ _ _ _ _ _ P hl hU
  obtain ⟨hLF, hLTD, hLEC, hGF, _, hGW, _, _⟩ := hC
  have key : ∀ (w : ArData.W Lc q) (n : ℕ),
      LocCount (↥(Dec (P.A w))) ((cycZ F Ω l).comp (Dec (P.A w)).subtype) n →
        LocCount (a.D w) (G.ε.comp (a.ι w)) n := by
    intro w n hn
    refine locCongr l (a.D w) (↥(Dec (P.A w))) (P.α w) (G.ε.comp (a.ι w))
      ((cycZ F Ω l).comp (Dec (P.A w)).subtype) n ?_ hn
    intro g
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [P.ι_eq w g, P.e_ε]
  have notl : ∀ (w : ArData.W Lc q), (∀ v, w ≠ Sum.inl v) →
      LocCount (a.D w) (G.ε.comp (a.ι w)) 0 := by
    intro w hw
    apply key
    refine (locBare hLF hLTD hLEC l F Ω (P.A w) (↑(P.pl w)) (P.isOver w)).2 ?_
    rw [P.pl_l]
    rintro ⟨v, hv⟩
    exact hw v hv
  have hcw : a.cw = fun i => P.e ((toGS Ω P.S) (P.c i)) := funext P.cw_eq
  refine ⟨?_, ?_, ?_, ?_, hU⟩
  · rw [hcw]
    exact gwBare hGW hLTD hGF hLF l F Ω P.S G.Γ P.e G.ε (ArData.W Lc q) P.pl P.A a.D a.ι P.α d P.ip P.c
      hl P.above P.e_ε P.isOver P.ι_eq P.cc
  · intro v
    have h1 := (locBare hLF hLTD hLEC l F Ω (P.A (Sum.inl v)) (↑(P.pl (Sum.inl v))) (P.isOver _)).1
      ((P.pl_l _).2 ⟨v, rfl⟩)
    rw [← P.dv_eq v] at h1
    exact key (Sum.inl v) _ h1
  · intro u
    exact notl (Sum.inr (Sum.inl u)) (fun v h => by cases h)
  · intro j
    exact notl (Sum.inr (Sum.inr j)) (fun v h => by cases h)

theorem UpperTheory.V.Pa.arSys :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (T : TWGrp (globOf r V0)) (_ : TWPl r T), V0.S' = s.S → Nonempty (ArSys T (Module.finrank ℚ (Lp L)) V0.frame.D0) := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r T P hS
  choose a p h1 h2 h3 using arPres l L Ω s V0 O n r T P hS
  exact ⟨{
    a := a
    counts := fun N =>
      presCounts hP l _ _ _ _ (a N) (Lp L) Ω (p N) s.odd (unrLoc l L Ω s V0 O n r)
    dv := fun v : Vl l L => locDeg v.1
    dv_eq := fun N => funext (h1 N)
    d0 := h2
    ph := fun N j => (h3 N j).1
    ta := fun N j => (h3 N j).2 }⟩

namespace UpperTheory.V.Pa

theorem b1Ar : FirstOrderDualArithmeticBound := by
  intro hcoh l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r T x0 x k al hS hloc _ hρ hN4 hE hD
  obtain ⟨d', hsum, hab⟩ := hloc
  obtain ⟨A⟩ := arSys hcoh l L Ω s V0 O n r T x0 hS
  refine _root_.UpperTheory.V.Pa.W1_bound_arithmetic_rank_two l (locOf r) (globOf r V0) T n x k al _ V0.frame.D0 A d' s.odd ?_ hab
    (arPl hcoh l L Ω s V0 O n r hS).1 hρ hN4 hE hD
  rw [← hsum]
  exact (finsum_eq_sum_of_fintype _).symm

end UpperTheory.V.Pa

end
