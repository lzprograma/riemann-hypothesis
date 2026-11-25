module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormaliseMeanSquareOfCocompact
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.SumHecke

open GlobalTheory.SplitScalar GlobalTheory.SplitHecke
open scoped ComplexOrder

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem infPart_cA (a : AE D) (h : infPart D a = 0) : infPart D (cA D a) = 0 := by
  have h1 := realIdem_mul_of_fin h
  have h2 : realIdem D * cA D a = 0 := by
    rw [← cA_realIdem, ← RingHom.map_mul, h1, RingHom.map_zero]
  have h3 := congrArg (infPart D) h2
  rwa [RingHom.map_mul, infPart_realIdem, one_mul, RingHom.map_zero] at h3

theorem isoIdem_of_isOrthSum {e : AE D} (he : GlobalTheory.PlaceModelSum.IsOrthSum e) (hec : e * cA D e = 0) :
    IsoIdem e :=
  ⟨he.idem, hec, he.infPart_eq, infPart_cA e he.infPart_eq⟩

theorem cut_exists (V : HSp D) (g : GA D V) (ε : AE D) (hεε : ε * ε = ε) (hε : cA D ε = ε) :
    ∃ k : GA D V, mt V k = ε • mt V g + (1 - ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  set M := mt V g with hM
  have hinv : M * ((matHom V g)⁻¹).1 = 1 := (matHom V g).mul_inv
  have hinv' : ((matHom V g)⁻¹).1 * M = 1 := (matHom V g).inv_mul
  let K : GL (Fin V.rank) (AE D) := ⟨ε • M + (1 - ε) • 1, ε • ((matHom V g)⁻¹).1 + (1 - ε) • 1,
    GlobalTheory.GfCut.idem_mul ε hεε _ _ hinv, GlobalTheory.GfCut.idem_mul ε hεε _ _ hinv'⟩
  have hgU : Formalism.UG.cT (cA D) M * V.gram.map (incA D) * M = V.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have hKU : K ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
    GlobalTheory.GfCut.idem_unitary (cA D) ε hε hεε _ M hgU
  exact ⟨(⟨K, hKU⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram), rfl⟩

theorem cut_mul {R : Type} [CommRing R] {n : ℕ} (e f : R) (hef : e * f = 0) (M : Matrix (Fin n) (Fin n) R) :
    (e • M + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) * (f • M + (1 - f) • 1) = (e + f) • M + (1 - (e + f)) • 1 := by
  have h1 : e * (1 - f) = e := by rw [mul_sub, mul_one, hef, sub_zero]
  have h2 : (1 - e) * f = f := by rw [sub_mul, one_mul, hef, sub_zero]
  have h3 : (1 - e) * (1 - f) = 1 - (e + f) := by linear_combination hef
  simp only [add_mul, mul_add, smul_mul_smul_comm, Matrix.mul_one, Matrix.one_mul, hef, h1, h2, h3, zero_smul, zero_add]
  rw [add_smul]; abel

theorem idem_det {R : Type} [CommRing R] {n : ℕ} {a ε : R} (ha : a * a = a) (haε : a * ε = a)
    (M : Matrix (Fin n) (Fin n) R) : a * (ε • M + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)).det = a * M.det := by
  have h0 : a * a ^ Fintype.card (Fin n) = a := by
    rw [← pow_succ']
    exact IsIdempotentElem.pow_succ_eq _ ha
  have h1 : a • (ε • M + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) = a • M := by
    rw [smul_add, smul_smul, smul_smul, mul_sub, haε, mul_one, sub_self, zero_smul, add_zero]
  rw [← h0, mul_assoc, mul_assoc, ← Matrix.det_smul, ← Matrix.det_smul, h1]

theorem cut_supp {R : Type} [CommRing R] {n : ℕ} {ε : R} (hε : ε * ε = ε) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    ε * ((ε • M + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) - 1) i j =
      ((ε • M + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R)) - 1) i j := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * hε

theorem det_parts {R : Type} [CommRing R] {a b d d₁ d₂ x x₁ x₂ : R} (hab : a * b = 0)
    (h : x = (a + b) * d + (1 - (a + b))) (h₁ : x₁ = a * d₁ + (1 - a)) (h₂ : x₂ = b * d₂ + (1 - b))
    (k₁ : a * d₁ = a * d) (k₂ : b * d₂ = b * d) : x = x₁ * x₂ := by
  rw [h, h₁, h₂, k₁, k₂]
  linear_combination (-(d - 1) ^ 2) * hab

theorem exists_detAt {a : AE D} (ha : a * a = a) (V : HSp D) (g : GA D V) : ∃ x, IsDetAt a V g x := by
  have h : (mt V g).det * (mt V g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, show mt V g * mt V g⁻¹ = 1 from (matHom V g).mul_inv, Matrix.det_one]
  have h2 : (a * (mt V g).det + (1 - a)) * (a * (mt V g⁻¹).det + (1 - a)) = 1 := by
    linear_combination ((mt V g).det * (mt V g⁻¹).det - (mt V g).det - (mt V g⁻¹).det + 1) * ha + a * h
  exact ⟨⟨_, _, h2, by rw [mul_comm, h2]⟩, rfl⟩

def SplitLaw (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (e : AE D) : Prop :=
  ∀ g x, SuppAt e S g → IsDetAt e S g x → FormLaw ψ om e g 1 (splitFacO χS χT x 1)

variable {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem splitLaw_split (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} (he : IsSplitIdem D e) :
    SplitLaw ψ χS χT om e := fun g x hg hx =>
  hW.om_split e he g 1 hg (fun i j => by
    rw [show mt T 1 = 1 from rfl, sub_self, Matrix.zero_apply, mul_zero]) x 1 hx (by
    show (1 : AE D) = _
    rw [show mt T 1 = 1 from rfl, Matrix.det_one]; ring)

theorem splitLaw_zero : SplitLaw ψ χS χT om (0 : AE D) := by
  intro g x hg hx
  have h1 : g = 1 := by
    refine Subtype.ext (Units.ext ?_)
    show mt S g = 1
    rw [← sub_eq_zero]
    ext i j
    rw [← hg i j, RingHom.map_zero, add_zero, zero_mul, Matrix.zero_apply]
  have h2 : x = 1 := Units.ext (by rw [show (x : AE D) = _ from hx, zero_mul, zero_add, sub_zero, Units.val_one])
  subst h1 h2
  refine ⟨1, one_pos, fun ℓ _ f _ => ?_⟩
  rw [show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one, splitFacO, map_one, map_one, inv_one, mul_one]
  simp

theorem isHalf_add_left {m n : ℕ} {a b : AE D} (hab : a * b = 0) {u : Mx D m n} (hu : IsHalf a u) :
    IsHalf (a + b) u := fun i j => by
  rw [add_mul, hu i j, ← hu i j, ← mul_assoc, mul_comm b, hab, zero_mul, add_zero]


theorem splitLaw_add (hW : IsWeilDatumO ψ S T χS χT om) {a b : AE D} (ha : a * a = a) (hb : b * b = b)
    (hac : a * cA D a = 0) (hbc : b * cA D b = 0) (hab : a * b = 0) (habc : a * cA D b = 0)
    (la : SplitLaw ψ χS χT om a) (lb : SplitLaw ψ χS χT om b) : SplitLaw ψ χS χT om (a + b) := by
  intro g x hg hx
  have cc := @GlobalTheory.DualPairCheck.cA_cA D
  have ha' : cA D a * cA D a = cA D a := by rw [← RingHom.map_mul, ha]
  have hb' : cA D b * cA D b = cA D b := by rw [← RingHom.map_mul, hb]
  have hab' : cA D a * cA D b = 0 := by rw [← RingHom.map_mul, hab, RingHom.map_zero]
  have hcab : cA D a * b = 0 := by
    have := congrArg (cA D) habc
    rwa [RingHom.map_mul, cc, RingHom.map_zero] at this
  have ea : (a + cA D a) * (a + cA D a) = a + cA D a := by linear_combination ha + ha' + 2 * hac
  have eb : (b + cA D b) * (b + cA D b) = b + cA D b := by linear_combination hb + hb' + 2 * hbc
  have eab : (a + cA D a) * (b + cA D b) = 0 := by linear_combination hab + hab' + habc + hcab
  obtain ⟨g₁, hg₁⟩ := cut_exists S g _ ea (by rw [RingHom.map_add (f := _), cc, add_comm])
  obtain ⟨g₂, hg₂⟩ := cut_exists S g _ eb (by rw [RingHom.map_add (f := _), cc, add_comm])
  have hgg : g = g₁ * g₂ := by
    refine Subtype.ext (Units.ext ?_)
    show mt S g = mt S g₁ * mt S g₂
    rw [hg₁, hg₂, cut_mul _ _ eab]
    ext i j
    have := hg i j
    rw [RingHom.map_add (f := _), Matrix.sub_apply] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination -this
  obtain ⟨x₁, hx₁⟩ := exists_detAt ha S g₁
  obtain ⟨x₂, hx₂⟩ := exists_detAt hb S g₂
  obtain ⟨r₁, hr₁, l₁⟩ := la g₁ x₁ (fun i j => by rw [hg₁]; exact cut_supp ea _ i j) hx₁
  obtain ⟨r₂, hr₂, l₂⟩ := lb g₂ x₂ (fun i j => by rw [hg₂]; exact cut_supp eb _ i j) hx₂
  have hxx : x = x₁ * x₂ := by
    refine Units.ext (det_parts hab hx hx₁ hx₂ ?_ ?_)
    · rw [hg₁]
      exact idem_det ha (by rw [mul_add, ha, hac, add_zero]) _
    · rw [hg₂]
      exact idem_det hb (by rw [mul_add, hb, hbc, add_zero]) _
  refine ⟨r₁ * r₂, mul_pos hr₁ hr₂, fun ℓ hℓ f hf => ?_⟩
  rw [RingHom.map_add (f := _)] at hℓ
  have e1 : om (g, 1) f = om (g₁, 1) (om (g₂, 1) f) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, ← hgg]
  rw [e1, l₁ ℓ (fun u hu => hℓ u (isHalf_add_left hab' hu)) _ (hW.om_pres _ _ hf),
    l₂ ℓ (fun u hu => hℓ u (by rw [add_comm]; exact isHalf_add_left (by rw [mul_comm, hab']) hu)) _ hf, hxx]
  simp only [splitFacO, map_mul, map_one, mul_one, mul_inv, Circle.coe_mul, Complex.ofReal_mul]
  ring

theorem splitLaw_sum (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} (he : GlobalTheory.PlaceModelSum.IsOrthSum e)
    (hec : e * cA D e = 0) : SplitLaw ψ χS χT om e := by
  classical
  obtain ⟨ι, P, es, h1, h2, rfl⟩ := he
  induction P using Finset.induction_on with
  | empty => exact splitLaw_zero
  | insert i P hi ih =>
    have h1' : ∀ j ∈ P, IsSplitIdem D (es j) := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have h2' : ∀ j ∈ P, ∀ k ∈ P, k ≠ j → es j * es k = 0 := fun j hj k hk =>
      h2 j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    have hi' := h1 i (Finset.mem_insert_self i P)
    have hb : (∑ j ∈ P, es j) * ∑ j ∈ P, es j = ∑ j ∈ P, es j :=
      GlobalTheory.PlaceModelSum.IsOrthSum.idem ⟨ι, P, es, h1', h2', rfl⟩
    have hab : es i * ∑ j ∈ P, es j = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => h2 i (Finset.mem_insert_self i P) j (Finset.mem_insert_of_mem hj)
        fun h => hi (h ▸ hj)
    rw [Finset.sum_insert hi] at hec ⊢
    generalize (∑ j ∈ P, es j) = b at *
    have hb' : cA D b * cA D b = cA D b := by rw [← RingHom.map_mul, hb]
    have hab' : cA D (es i) * cA D b = 0 := by rw [← RingHom.map_mul, hab, RingHom.map_zero]
    rw [RingHom.map_add (f := _)] at hec
    have hbc : b * cA D b = 0 := by
      have : b * cA D b = (b * (es i + b)) * (cA D b * (cA D (es i) + cA D b)) := by
        rw [mul_add, mul_add, mul_comm b (es i), hab, hb, mul_comm (cA D b) (cA D (es i)), hab', hb', zero_add, zero_add]
      rw [this, mul_mul_mul_comm, hec, mul_zero]
    have habc : es i * cA D b = 0 := by
      have : es i * cA D b = (es i * (es i + b)) * (cA D b * (cA D (es i) + cA D b)) := by
        rw [mul_add, mul_add, hab, hi'.1, mul_comm (cA D b) (cA D (es i)), hab', hb', zero_add, add_zero]
      rw [this, mul_mul_mul_comm, hec, mul_zero]
    exact splitLaw_add hW hi'.1 hb hi'.2.1 hbc hab habc (splitLaw_split hW hi') (ih h1' h2' hbc)

end GlobalTheory.SumHecke
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem GlobalTheory.SumHecke.om_eq_sum_idemSum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ (g : GA D S) (x : (AE D)ˣ), SuppAt e S g → IsDetAt (cA D e) S g x → ∀ (R : Finset (WO S T)), (∀ u ∈ R, actO S T g⁻¹ 1 u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) u) → (∀ w, actO S T g⁻¹ 1 w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → IsHalf (cA D e) w → ∃! v, v ∈ R ∧ w - v ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) → (∀ w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True), IsHalf (cA D e) w → actO S T g⁻¹ 1 w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) → ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → heisO ψ S T u f = f) → om (g, 1) f = ((splitFacO χS χT x 1 : ℂ) * ((Real.sqrt (R.card : ℝ) : ℝ) : ℂ)⁻¹) • ∑ u ∈ R, heisO ψ S T u f := by
  intro D ψ S T χS χT om hW ΛS ΛT hS hT Q e he g x hg hx R hR hRu hle f hf hfix
  have cc := @GlobalTheory.DualPairCheck.cA_cA D
  have ho := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).conj
  have hec : cA D e * cA D (cA D e) = 0 := by rw [cc, mul_comm, he.2]
  have hz := GlobalTheory.SumHecke.splitLaw_sum hW ho hec g x (fun i j => by rw [cc, add_comm]; exact hg i j) hx
  refine GlobalTheory.SplitHecke.om_eq_sum_iso hW hS hT (GlobalTheory.SumHecke.isoIdem_of_isOrthSum ho hec) hf
    (fun u hu h => hfix u hu (by rw [cc] at h; exact h.symm)) hz ?_ ?_ ?_ <;> rw [inv_one] <;> assumption

end

end
