module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.SConjSpaceC
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliOperatorAlgebraStableUnderComplexConj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicGLHomeomorphInfiniteFinite
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousMapGL
import GroundTheory.AutomorphicForms.GLnLocal
import GroundTheory.GlobalFields.LocalFieldAtPlace

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep

namespace UpperTheory.CBC.SConjSpaceCAux

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]


open Classical in
def cc (τ : E →+* ℂ) : Cinf E →+* ℂ :=
  if (InfinitePlace.mk τ).embedding = τ then Pi.evalRingHom (fun _ => ℂ) (InfinitePlace.mk τ)
  else (starRingEnd ℂ).comp (Pi.evalRingHom (fun _ => ℂ) (InfinitePlace.mk τ))

theorem cc_of_eq {τ : E →+* ℂ} (h : (InfinitePlace.mk τ).embedding = τ) (x : Cinf E) :
    cc τ x = x (InfinitePlace.mk τ) := by
  classical
  unfold cc; rw [ite_eq_left h]; rfl

theorem cc_of_ne {τ : E →+* ℂ} (h : ¬ (InfinitePlace.mk τ).embedding = τ) (x : Cinf E) :
    cc τ x = starRingEnd ℂ (x (InfinitePlace.mk τ)) := by
  classical
  unfold cc; rw [ite_eq_right h]; rfl

theorem cc_embedding (w : InfinitePlace E) (x : Cinf E) : cc w.embedding x = x w := by
  have h : (InfinitePlace.mk w.embedding).embedding = w.embedding := by rw [InfinitePlace.mk_embedding]
  rw [cc_of_eq h, InfinitePlace.mk_embedding]

theorem cc_ext {x y : Cinf E} (h : ∀ τ, cc τ x = cc τ y) : x = y :=
  funext fun w => (cc_embedding w x).symm.trans ((h _).trans (cc_embedding w y))

theorem conj_ne (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
  NumberField.IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)

theorem cc_conj (τ : E →+* ℂ) (x : Cinf E) :
    cc (ComplexEmbedding.conjugate τ) x = starRingEnd ℂ (cc τ x) := by
  have hm := InfinitePlace.mk_conjugate_eq τ
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · have h' : ¬ (InfinitePlace.mk (ComplexEmbedding.conjugate τ)).embedding = ComplexEmbedding.conjugate τ := by
      rw [hm, h]; exact (conj_ne τ).symm
    rw [cc_of_ne h', cc_of_eq h, hm]
  · have h2 : (InfinitePlace.mk τ).embedding = ComplexEmbedding.conjugate τ :=
      (InfinitePlace.embedding_mk_eq τ).resolve_left h
    have h' : (InfinitePlace.mk (ComplexEmbedding.conjugate τ)).embedding = ComplexEmbedding.conjugate τ := by
      rw [hm, h2]
    rw [cc_of_eq h', cc_of_ne h, hm, starRingEnd_self_apply]

theorem cc_star (τ : E →+* ℂ) (x : Cinf E) : cc τ (star x) = starRingEnd ℂ (cc τ x) := by
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · rw [cc_of_eq h, cc_of_eq h]; rfl
  · rw [cc_of_ne h, cc_of_ne h]; rfl

theorem cc_smul (τ : E →+* ℂ) (r : ℝ) (x : Cinf E) : cc τ (r • x) = r • cc τ x := by
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · rw [cc_of_eq h, cc_of_eq h]; rfl
  · rw [cc_of_ne h, cc_of_ne h]
    change starRingEnd ℂ (r • x (InfinitePlace.mk τ)) = _
    rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]

theorem continuous_cc (τ : E →+* ℂ) : Continuous (cc τ) := by
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · have e : (cc τ : Cinf E → ℂ) = fun x => x (InfinitePlace.mk τ) := funext (cc_of_eq h)
    rw [e]; exact continuous_apply _
  · have e : (cc τ : Cinf E → ℂ) = fun x => starRingEnd ℂ (x (InfinitePlace.mk τ)) := funext (cc_of_ne h)
    rw [e]; exact Complex.continuous_conj.comp (continuous_apply _)

theorem cc_pInf_alg (τ : E →+* ℂ) (m : E) : cc τ (pInf E (algebraMap E (Ad E) m)) = τ m := by
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · rw [cc_of_eq h, pInf_algebraMap, h]
  · have h2 : (InfinitePlace.mk τ).embedding = ComplexEmbedding.conjugate τ :=
      (InfinitePlace.embedding_mk_eq τ).resolve_left h
    rw [cc_of_ne h, pInf_algebraMap, h2, ComplexEmbedding.conjugate_coe_eq, starRingEnd_self_apply]

theorem cc_eq_zero {τ : E →+* ℂ} {x : Cinf E} (hx : x (InfinitePlace.mk τ) = 0) : cc τ x = 0 := by
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · rw [cc_of_eq h, hx]
  · rw [cc_of_ne h, hx, map_zero]

theorem eq_atEmb {τ : E →+* ℂ} {z : ℂ} {x : Cinf E} (h0 : ∀ w, w ≠ InfinitePlace.mk τ → x w = 0)
    (h1 : cc τ x = z) : x = atEmb τ z := by
  classical
  funext w
  have e : atEmb τ z = Pi.single (InfinitePlace.mk τ)
      (if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z) := rfl
  rw [e]
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw
    rw [Pi.single_eq_same]
    by_cases h : (InfinitePlace.mk τ).embedding = τ
    · rw [ite_eq_left h, ← h1, cc_of_eq h]
    · rw [ite_eq_right h, ← h1, cc_of_ne h, starRingEnd_self_apply]
  · rw [Pi.single_eq_of_ne hw, h0 w hw]

theorem atEmb_apply_ne {τ : E →+* ℂ} (z : ℂ) {w : InfinitePlace E} (hw : w ≠ InfinitePlace.mk τ) :
    atEmb τ z w = 0 := by
  classical
  have e : atEmb τ z = Pi.single (InfinitePlace.mk τ)
      (if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z) := rfl
  rw [e, Pi.single_eq_of_ne hw]

theorem cc_atEmb (τ : E →+* ℂ) (z : ℂ) : cc τ (atEmb τ z) = z := by
  classical
  have e : atEmb τ z = Pi.single (InfinitePlace.mk τ)
      (if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z) := rfl
  by_cases h : (InfinitePlace.mk τ).embedding = τ
  · rw [cc_of_eq h, e, Pi.single_eq_same, ite_eq_left h]
  · rw [cc_of_ne h, e, Pi.single_eq_same, ite_eq_right h, starRingEnd_self_apply]

def Lx (σ : E ≃+* E) : Cinf E →+* Cinf E := RingHom.pi fun w => cc (w.embedding.comp (σ : E →+* E))

theorem cc_Lx (σ : E ≃+* E) (ρ : E →+* ℂ) (x : Cinf E) : cc ρ (Lx σ x) = cc (ρ.comp (σ : E →+* E)) x := by
  by_cases h : (InfinitePlace.mk ρ).embedding = ρ
  · rw [cc_of_eq h]
    change cc (((InfinitePlace.mk ρ).embedding).comp (σ : E →+* E)) x = _
    rw [h]
  · have h2 : (InfinitePlace.mk ρ).embedding = ComplexEmbedding.conjugate ρ :=
      (InfinitePlace.embedding_mk_eq ρ).resolve_left h
    rw [cc_of_ne h]
    change starRingEnd ℂ (cc (((InfinitePlace.mk ρ).embedding).comp (σ : E →+* E)) x) = _
    have e : (ComplexEmbedding.conjugate ρ).comp (σ : E →+* E) = ComplexEmbedding.conjugate (ρ.comp (σ : E →+* E)) :=
      RingHom.ext fun _ => rfl
    rw [h2, e, cc_conj, starRingEnd_self_apply]

theorem Lx_symm (σ : E ≃+* E) (x : Cinf E) : Lx σ (Lx σ.symm x) = x :=
  cc_ext fun ρ => by
    have e : (ρ.comp (σ : E →+* E)).comp (σ.symm : E →+* E) = ρ := RingHom.ext fun y => by
      change ρ (σ (σ.symm y)) = ρ y
      rw [RingEquiv.apply_symm_apply]
    rw [cc_Lx, cc_Lx, e]

theorem Lx_symm' (σ : E ≃+* E) (x : Cinf E) : Lx σ.symm (Lx σ x) = x := by
  simpa using Lx_symm σ.symm x

theorem continuous_Lx (σ : E ≃+* E) : Continuous (Lx σ) :=
  continuous_pi fun w => continuous_cc _

theorem Lx_smul (σ : E ≃+* E) (r : ℝ) (x : Cinf E) : Lx σ (r • x) = r • Lx σ x :=
  funext fun w => cc_smul _ r x

theorem Lx_star (σ : E ≃+* E) (x : Cinf E) : Lx σ (star x) = star (Lx σ x) :=
  funext fun w => cc_star _ x

theorem Lx_atEmb (σ : E ≃+* E) (τ : E →+* ℂ) (z : ℂ) :
    Lx σ (atEmb τ z) = atEmb (τ.comp (σ.symm : E →+* E)) z := by
  have hτ : (τ.comp (σ.symm : E →+* E)).comp (σ : E →+* E) = τ := RingHom.ext fun y => by
    change τ (σ.symm (σ y)) = τ y
    rw [RingEquiv.symm_apply_apply]
  refine eq_atEmb (fun w hw => ?_) (by rw [cc_Lx, hτ, cc_atEmb])
  change cc (w.embedding.comp (σ : E →+* E)) (atEmb τ z) = 0
  refine cc_eq_zero (atEmb_apply_ne z fun e => hw ?_)
  rcases InfinitePlace.mk_eq_iff.1 e with e' | e'
  · rw [← InfinitePlace.mk_embedding w]
    congr 1
    refine RingHom.ext fun y => ?_
    have := congrArg (fun f : E →+* ℂ => f (σ.symm y)) e'
    change w.embedding (σ (σ.symm y)) = τ (σ.symm y) at this
    rw [RingEquiv.apply_symm_apply] at this
    exact this
  · rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_conjugate_eq]
    congr 1
    refine RingHom.ext fun y => ?_
    have := congrArg (fun f : E →+* ℂ => f (σ.symm y)) e'
    change starRingEnd ℂ (w.embedding (σ (σ.symm y))) = τ (σ.symm y) at this
    rw [RingEquiv.apply_symm_apply] at this
    exact this

theorem conjFin_symm_conjFin (c : E ≃+* E) (x : Af E) : conjFin c.symm (conjFin c x) = x := by
  have key : ∀ (v w : HeightOneSpectrum (𝓞 E)) (_ : w = v) (f : w.adicCompletion E → v.adicCompletion E),
      Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → f (pLoc E w x) = pLoc E v x := by
    rintro _ v rfl f hf h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext h)) _
  refine FiniteAdeleRing.ext _ fun v => ?_
  change pLoc E v (conjFin c.symm (conjFin c x)) = pLoc E v x
  rw [pLoc_conjFin, pLoc_conjFin]
  refine key v _ ?_ (conjLoc c.symm v ∘ conjLoc c _) ((conjLoc_spec _ _).1.comp (conjLoc_spec _ _).1) fun k => ?_
  · refine (eq_conjSrc (c := c) fun k => ?_).symm
    have h1 := (conjLoc_spec c.symm v).2.2 (algebraMap E _ (c k))
    rw [(conjLoc_spec c.symm v).2.1, RingEquiv.symm_apply_apply] at h1
    have e1 : Valued.v (algebraMap E (v.adicCompletion E) k) = v.valuation E k := v.valuedAdicCompletion_eq_valuation' k
    have e2 : Valued.v (algebraMap E ((conjSrc c.symm v).adicCompletion E) (c k)) = (conjSrc c.symm v).valuation E (c k) :=
      (conjSrc c.symm v).valuedAdicCompletion_eq_valuation' (c k)
    rw [e1, e2] at h1
    exact h1.symm
  · rw [Function.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1, RingEquiv.symm_apply_apply]

structure GD (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] where
  σ : E ≃+* E
  s : Ad E ≃+* Ad E
  c : Af E ≃+* Af E
  cont : Continuous s
  cont' : Continuous s.symm
  contc : Continuous c
  contc' : Continuous c.symm
  inf : ∀ x, pInf E (s x) = Lx σ (pInf E x)
  fin : ∀ x, pFin E (s x) = c (pFin E x)
  rat : ∀ x : E, s (algebraMap E (Ad E) x) = algebraMap E (Ad E) (σ x)

def GD.symm (d : GD E) : GD E where
  σ := d.σ.symm
  s := d.s.symm
  c := d.c.symm
  cont := d.cont'
  cont' := d.cont
  contc := d.contc'
  contc' := d.contc
  inf x := by
    have h := d.inf (d.s.symm x)
    rw [RingEquiv.apply_symm_apply] at h
    rw [h, Lx_symm']
  fin x := by
    have h := d.fin (d.s.symm x)
    rw [RingEquiv.apply_symm_apply] at h
    rw [h, RingEquiv.symm_apply_apply]
  rat x := by
    rw [RingEquiv.symm_apply_eq, d.rat, RingEquiv.apply_symm_apply]

theorem pInf_sInf (z : Cinf E) : pInf E (sInf E z) = z := (infEq E).symm_apply_apply z

theorem pFin_sInf (z : Cinf E) : pFin E (sInf E z) = 0 := rfl

theorem pInf_sFin (z : Af E) : pInf E (sFin E z) = 0 := map_zero (infEq E).symm

theorem pFin_sFin (z : Af E) : pFin E (sFin E z) = z := rfl

theorem ad_decomp (x : Ad E) : x = sInf E (pInf E x) + sFin E (pFin E x) :=
  ad_ext (by rw [map_add (f := _), pInf_sInf, pInf_sFin, add_zero]) (by rw [map_add (f := _), pFin_sInf, pFin_sFin, zero_add])

theorem exists_GD (σ : E ≃+* E) (s : Ad E ≃+* Ad E) (h : IsGalAd σ s) : ∃ d : GD E, d.s = s ∧ d.σ = σ := by
  obtain ⟨hc, hr, hf⟩ := h
  have hfin : ∀ x, pFin E (s x) = conjFin σ (pFin E x) := hf
  obtain ⟨L0, hL0⟩ : ∃ L0 : Cinf E → Cinf E, ∀ y, L0 y = pInf E (s (sInf E y)) := ⟨_, fun _ => rfl⟩
  have hsInf : ∀ y, s (sInf E y) = sInf E (L0 y) := fun y =>
    ad_ext (by rw [pInf_sInf, hL0]) (by rw [hfin, pFin_sInf, pFin_sInf, map_zero])
  have hadd : ∀ y y', L0 (y + y') = L0 y + L0 y' := fun y y' => by
    rw [hL0, hL0, hL0, map_add (f := _), map_add (f := _), map_add (f := _)]
  have hmul : ∀ y y', L0 (y * y') = L0 y * L0 y' := fun y y' => by
    rw [hL0, hL0, hL0, map_mul, map_mul, map_mul]
  have hcont : Continuous L0 := by
    have e : L0 = fun y => pInf E (s (sInf E y)) := funext hL0
    rw [e]
    exact (GlobalTheory.CuspRep.GASplit.continuous_pInf E).comp (hc.comp (GlobalTheory.CuspRep.GASplit.continuous_sInf E))
  let A : Cinf E →+ Cinf E :=
    { toFun := L0
      map_zero' := by rw [hL0, map_zero, map_zero, map_zero]
      map_add' := hadd }
  let Lin : Cinf E →ₗ[ℝ] Cinf E :=
    { toFun := L0
      map_add' := hadd
      map_smul' := fun r y => map_real_smul A hcont r y }
  have hinj : Function.Injective Lin := fun y y' e => by
    have e1 : s (sInf E y) = s (sInf E y') := by
      rw [hsInf, hsInf]; exact congrArg (sInf E) e
    have e2 := congrArg (pInf E) (s.injective e1)
    rwa [pInf_sInf, pInf_sInf] at e2
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
  have hy' : L0 y = 1 := hy
  have h1 : L0 1 = 1 := by
    calc L0 1 = L0 1 * L0 y := by rw [hy', mul_one]
      _ = L0 y := by rw [← hmul, one_mul]
      _ = 1 := hy'
  have hs1 : s (sInf E 1) = sInf E 1 := by rw [hsInf, h1]
  have hsFin : ∀ z, pInf E (s (sFin E z)) = 0 := fun z => by
    have e : sFin E z = sFin E z * (1 - sInf E 1) :=
      ad_ext (by rw [map_mul, pInf_sFin, zero_mul])
        (by rw [map_mul, map_sub, map_one, pFin_sFin, pFin_sInf, sub_zero, mul_one])
    rw [e, map_mul, map_mul, map_sub, map_one, map_sub, map_one, hs1, pInf_sInf, sub_self, mul_zero]
  have hinf0 : ∀ x, pInf E (s x) = L0 (pInf E x) := fun x => by
    conv_lhs => rw [ad_decomp x]
    rw [map_add (f := _), map_add (f := _), hsFin, add_zero, hL0]
  have hD : DenseRange fun m : E => pInf E (algebraMap E (Ad E) m) := by
    have e : (fun m : E => pInf E (algebraMap E (Ad E) m)) =
        (infEq E).symm ∘ algebraMap E (InfiniteAdeleRing E) := rfl
    rw [e]
    exact (infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E)
      (GlobalTheory.CuspRep.GASplit.continuous_infEq_symm E)
  have heq : L0 = Lx σ := hD.equalizer hcont (continuous_Lx σ) (funext fun m => by
    change L0 (pInf E (algebraMap E (Ad E) m)) = Lx σ (pInf E (algebraMap E (Ad E) m))
    rw [← hinf0, hr]
    refine cc_ext fun ρ => ?_
    rw [cc_Lx, cc_pInf_alg, cc_pInf_alg]
    rfl)
  have hinf : ∀ x, pInf E (s x) = Lx σ (pInf E x) := fun x => by rw [hinf0, heq]
  let c : Af E ≃+* Af E :=
    { toFun := conjFin σ
      invFun := conjFin σ.symm
      left_inv := conjFin_symm_conjFin σ
      right_inv := fun x => by
        have := conjFin_symm_conjFin σ.symm x
        rwa [RingEquiv.symm_symm] at this
      map_mul' := map_mul _
      map_add' := map_add _ }
  have hsymm : ∀ x, s.symm x = sInf E (Lx σ.symm (pInf E x)) + sFin E (conjFin σ.symm (pFin E x)) := fun x => by
    rw [RingEquiv.symm_apply_eq]
    refine ad_ext ?_ ?_
    · rw [hinf, map_add (f := _), pInf_sInf, pInf_sFin, add_zero, Lx_symm]
    · rw [hfin, map_add (f := _), pFin_sInf, pFin_sFin, zero_add]
      have := conjFin_symm_conjFin σ.symm (pFin E x)
      rw [RingEquiv.symm_symm] at this
      exact this.symm
  have hcont' : Continuous s.symm := by
    have e : (s.symm : Ad E → Ad E) =
        fun x => sInf E (Lx σ.symm (pInf E x)) + sFin E (conjFin σ.symm (pFin E x)) := funext hsymm
    rw [e]
    exact ((GlobalTheory.CuspRep.GASplit.continuous_sInf E).comp ((continuous_Lx _).comp (GlobalTheory.CuspRep.GASplit.continuous_pInf E))).add
      ((GlobalTheory.CuspRep.GASplit.continuous_sFin E).comp ((continuous_conjFin _).comp (GlobalTheory.CuspRep.GASplit.continuous_pFin E)))
  exact ⟨⟨σ, s, c, hc, hcont', continuous_conjFin σ, continuous_conjFin σ.symm, hinf, hfin, hr⟩, rfl, rfl⟩

section Pull

variable {a : ℕ} (d : GD E)

def SA (d : GD E) (a : ℕ) : GA E a →* GA E a := GeneralLinearGroup.map d.s.toRingHom

theorem SA_SA_symm (g : GA E a) : SA d a (SA d.symm a g) = g := by
  ext i j : 2
  exact d.s.apply_symm_apply _

theorem SA_symm_SA (g : GA E a) : SA d.symm a (SA d a g) = g := by
  ext i j : 2
  exact d.s.symm_apply_apply _

def LLm (σ : E ≃+* E) : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => Lx σ (X i j)
      map_add' := fun X Y => by funext i j; exact map_add _ _ _
      map_smul' := fun t X => by funext i j; exact Lx_smul σ t (X i j) }

def kMap (σ : E ≃+* E) (k : Kinf E a) : Kinf E a :=
  ⟨(RingHom.mapMatrix (Lx σ)) k.1, Matrix.mem_unitaryGroup_iff.2 (by
    have e : star ((RingHom.mapMatrix (Lx σ)) k.1) = (RingHom.mapMatrix (Lx σ)) (star k.1) := by
      ext i j : 1
      change star (Lx σ (k.1 j i)) = Lx σ (star (k.1 j i))
      rw [Lx_star]
    rw [e, ← map_mul, Matrix.mem_unitaryGroup_iff.1 k.2, map_one])⟩

def opMap (d : GD E) : Op E a → Op E a
  | .fin k => .fin (GeneralLinearGroup.map d.c.toRingHom k)
  | .cpt k => .cpt (kMap d.σ k)
  | .lie X => .lie (LLm d.σ X)

theorem opMap_opMap_symm (o : Op E a) : opMap d (opMap d.symm o) = o := by
  cases o with
  | fin k =>
    refine congrArg Op.fin (Units.ext (Matrix.ext fun i j => ?_))
    exact d.c.apply_symm_apply _
  | cpt k => exact congrArg Op.cpt (Subtype.ext (Matrix.ext fun i j => Lx_symm d.σ _))
  | lie X => exact congrArg Op.lie (funext fun i => funext fun j => Lx_symm d.σ _)

theorem height_eq (y : GL (Fin a) (Cinf E)) : height y = 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖ := rfl

theorem one_le_height (y : GL (Fin a) (Cinf E)) : 1 ≤ height y := by
  rw [height_eq]
  linarith [norm_nonneg (toL y.val), norm_nonneg (toL (y⁻¹).val)]

theorem height_map_le : ∃ K : ℝ, 1 ≤ K ∧ ∀ y : GL (Fin a) (Cinf E),
    height (GeneralLinearGroup.map (Lx d.σ) y) ≤ K * height y := by
  refine ⟨max 1 ‖LLm (a := a) d.σ‖, le_max_left _ _, fun y => ?_⟩
  have h1 : ∀ y : GL (Fin a) (Cinf E),
      ‖toL (GeneralLinearGroup.map (Lx d.σ) y).val‖ ≤ ‖LLm (a := a) d.σ‖ * ‖toL y.val‖ := fun y =>
    (LLm d.σ).le_opNorm (toL y.val)
  have hK : ‖LLm (a := a) d.σ‖ ≤ max 1 ‖LLm (a := a) d.σ‖ := le_max_right _ _
  have hK1 : (1 : ℝ) ≤ max 1 ‖LLm (a := a) d.σ‖ := le_max_left _ _
  rw [height_eq, height_eq, ← map_inv]
  have a1 := h1 y
  have a2 := h1 y⁻¹
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  nlinarith

theorem mem_ratN_alt {r : ℕ} {x : BlockIx a r → Ad E} (hx : x ∈ ratN E a r) : (fun p => d.s (x p)) ∈ ratN E a r := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨fun p => d.σ (y p), funext fun p => (d.rat (y p)).symm⟩

def gdData (d : GD E) (a : ℕ) : GlobalTheory.IsoPull.PullData E E a where
  eRat := d.σ.toRingHom
  eAd := d.s
  cont_eAd := d.cont
  cont_eAd_symm := d.cont'
  eAd_alg := d.rat
  eAd_rat := mem_ratN_alt d
  eAd_symm_rat := mem_ratN_alt d.symm
  eInf := Lx d.σ
  eFin := d.c.toRingHom
  cont_eFin := d.contc
  pInf_eAd := d.inf
  pFin_eAd := d.fin
  mapL := LLm d.σ
  mapL_apply _ _ _ := rfl
  mapOp := opMap d
  mapOp_fin _ := rfl
  mapOp_cpt k := ⟨kMap d.σ k, rfl, Units.ext rfl⟩
  mapOp_lie _ := rfl
  height_le := height_map_le d
  embMap τ := τ.comp (d.σ.symm : E →+* E)
  eInf_atEmb := Lx_atEmb d.σ

theorem SA_infGL (y : GL (Fin a) (Cinf E)) :
    SA d a (infGL E a y) = infGL E a (GeneralLinearGroup.map (Lx d.σ) y) :=
  (gdData d a).mapA_infGL y

theorem SA_finGL (k : GL (Fin a) (Af E)) :
    SA d a (finGL E a k) = finGL E a (GeneralLinearGroup.map d.c.toRingHom k) :=
  (gdData d a).mapA_finGL k

theorem SA_ratGL (γ : GL (Fin a) E) :
    SA d a (ratGL E a γ) = ratGL E a (GeneralLinearGroup.map d.σ.toRingHom γ) :=
  (gdData d a).mapA_ratGL γ

theorem chart_pullS (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => φ (SA d a g)) g x = chart φ (SA d a g) (LLm d.σ x) ∧ LLm d.σ x ∈ invSet E a :=
  (gdData d a).chart_map φ g hx

theorem pullS_mem_Sm {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) : (fun g => φ (SA d a g)) ∈ Sm E a :=
  (gdData d a).map_mem_Sm hφ

def pull (d : GD E) (a : ℕ) : Sm E a ≃ₗ[ℂ] Sm E a := (gdData d a).pull (pullS_mem_Sm d.symm)

theorem pull_apply (φ : Sm E a) (g : GA E a) : (pull d a φ).1 g = φ.1 (SA d a g) := rfl

theorem rt_pull (h : GA E a) (φ : Sm E a) : rt E a h (pull d a φ) = pull d a (rt E a (SA d a h) φ) :=
  (gdData d a).rt_pull h φ

theorem lie_pull (X : Lie E a) (φ : Sm E a) : lie E a X (pull d a φ) = pull d a (lie E a (LLm d.σ X) φ) :=
  (gdData d a).lie_pull X φ

theorem act_pull (o : Op E a) (φ : Sm E a) : act o (pull d a φ) = pull d a (act (opMap d o) φ) :=
  (gdData d a).act_pull o φ

theorem pull_act (o : Op E a) (φ : Sm E a) : pull d a (act o φ) = act (opMap d.symm o) (pull d a φ) := by
  rw [act_pull, opMap_opMap_symm]

theorem Eop_pull (τ : E →+* ℂ) (i j : Fin a) (φ : Sm E a) :
    Eop τ i j (pull d a φ) = pull d a (Eop (τ.comp (d.σ.symm : E →+* E)) i j φ) :=
  (gdData d a).Eop_pull τ i j φ

theorem cap_pull (τ : E →+* ℂ) (u : ℂ) (φ : Sm E a) :
    cap τ u (pull d a φ) = pull d a (cap (τ.comp (d.σ.symm : E →+* E)) u φ) :=
  (gdData d a).cap_pull τ u φ

theorem Zalg_pull {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ z' ∈ Zalg E a, ∀ φ, z (pull d a φ) = pull d a (z' φ) :=
  (gdData d a).Zalg_pull hz

theorem isAutForm_pull {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (pull d a φ) :=
  (gdData d a).isAutForm_pull h

theorem isCuspidal_pull {φ : GA E a → ℂ} (hφ : IsCuspidal φ) : IsCuspidal fun g => φ (SA d a g) :=
  (gdData d a).isCuspidal_pull hφ

def pullSub (π : CuspSub E a) : CuspSub E a :=
  (gdData d a).pullSub (fun o => ⟨opMap d.symm o, pull_act d o⟩) π

end Pull

end UpperTheory.CBC.SConjSpaceCAux


open UpperTheory.CBC.SConjSpaceCAux in
theorem UpperTheory.CBC.SConjSpaceC_holds : UpperTheory.CBC.SConjSpaceC := by
  intro M _ _ _ σ s hs n P
  obtain ⟨d, rfl, rfl⟩ := exists_GD σ s hs
  refine ⟨pullSub d P, ?_⟩
  ext f
  constructor
  · rintro ⟨φ, ⟨ψ, hψ, rfl⟩, rfl⟩
    exact ⟨ψ.1, ⟨ψ, hψ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
    exact ⟨pull d n ψ, ⟨ψ, hψ, rfl⟩, rfl⟩
