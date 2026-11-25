module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariantCm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartGaussianInvariant
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.UnitsBorelSpace.BorelSpaceDoubledGroup
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MeasurableSh
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.ContinuousFrameUM
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.CountableProdSub
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalCoordinates.RationalCoordinateCountability.VaddInvBotProd
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

/-! # DoubledLagrangianContinuous: Consolidated global theta-kernel definitions and proofs (DoubledLagrangianContinuous). -/
@[expose] public section

open GlobalTheory.Doubling (absE)
open GlobalTheory.WeilSchrodinger (thetaTr)
open UpperTheory.TP.W (GoodK)

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.ThetaQuasiRatF
open MeasureTheory Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem thetaTr_ratWF_add_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E
  →ₐ[F] E) (B : Base F E),
    GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : WOF F E nS nT),
            thetaTr F co B.ψ Φ (ratWF γ + w) = B.ψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) w)) *
              thetaTr F co B.ψ Φ w := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ hA hB κ _ co hrat Φ _ γ w
  obtain ⟨y, z, hyz⟩ := hrat γ
  have hγ : ratWF γ = incM F γ := rfl
  have hform := co.form (incM F γ) w
  rw [symp_eq_symplOF' σ JS JT ξ₀ JA JB ξ hA hB, hyz] at hform
  unfold thetaTr Darboux.rho
  rw [map_add (f := _), hγ, hyz]
  set u : (κ → AF F) × (κ → AF F) :=
    (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) with hu
  set v := co.e w
  have law := GlobalTheory.ThetaQuasiRat.schr_schr B.ψ u v Φ
  have hinv : B.ψ (-(⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) *
      B.ψ (⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2)) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hsum : schr B.ψ (u + v) Φ =
      B.ψ (-(⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) • schr B.ψ u (schr B.ψ v Φ)
        := by
    rw [law, smul_smul, hinv, one_smul]
  have h2 : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  rw [hsum, GlobalTheory.ThetaQuasiRat.thetaSum_smul', hu, GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ hψ.1.2.2.1
    y z, ← hu,
    symplOHF, hform, h2]
end GlobalTheory.ThetaQuasiRatF
end

noncomputable section
open scoped NNReal Classical ComplexOrder
open MeasureTheory Filter Topology GlobalTheory.AdelicU GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.ThK (incV)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
abbrev _root_.GlobalTheory.T.doubled_lagrangian_continuous :=
  GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add_k

namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {d : SD_k σ} (R : RD_k d) (L : LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
def cMF_k (L : LD_k d) (δ : E) (c : (Fin L.n → AE F E) × AF F) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (uA_k L c.1) (aB_k L δ c.2) 0 ((uA_k L (-c.1))ᵀ.map (cA σ))
def cMF'_k (L : LD_k d) (δ : E) (c : (Fin L.n → AE F E) × AF F) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (uA_k L (-c.1)) (-(uA_k L (-c.1) * aB_k L δ c.2 * (uA_k L c.1)ᵀ.map (cA σ))) 0 ((uA_k L c.1)ᵀ.map
    (cA σ))
theorem cMF_mul_k (L : LD_k d) (δ : E) (c : (Fin L.n → AE F E) × AF F) : cMF_k (σ := σ) L δ c * cMF'_k L δ c = 1 := by
  have e1 := uA_mul_neg_k L c.1
  have e2 : (uA_k L (-c.1))ᵀ.map (cA σ) * (uA_k L c.1)ᵀ.map (cA σ) = 1 := by
    rw [← kunf.map_cA_mul, ← Matrix.transpose_mul, e1, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have e3 : uA_k L c.1 * -(uA_k L (-c.1) * aB_k L δ c.2 * (uA_k L c.1)ᵀ.map (cA σ)) +
      aB_k L δ c.2 * (uA_k L c.1)ᵀ.map (cA σ) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, neg_add_cancel]
  simp only [cMF_k, cMF'_k, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [e1, e2, e3, Matrix.fromBlocks_one]
theorem continuous_aB_k (L : LD_k d) (δ : E) :
    Continuous fun c : (Fin L.n → AE F E) × AF F => aB_k L δ c.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [aB_k, Matrix.single_apply]
  split_ifs
  · exact Continuous.smul (continuous_snd (X := Fin L.n → AE F E) (Y := AF F))
      (continuous_const (y := inclR (F := F) (E := E) (AF F) δ))
  · exact continuous_const
theorem continuous_cM_k (h : Hyp_k L nb uM nb' w₁ cM δ) : Continuous cM := by
  have hF : ∀ c, inFrame d.b (cM c) = cMF_k L δ c := inFrame_cM_k h
  have hN := ComplexParameterFamilyContinuity.continuous_unipotent_nilpotent L
  have hU : Continuous fun c : (Fin L.n → AE F E) × AF F => uA_k L c.1 :=
    continuous_const.add (hN.comp continuous_fst)
  have hUn : Continuous fun c : (Fin L.n → AE F E) × AF F => uA_k L (-c.1) :=
    continuous_const.add (hN.comp continuous_fst.neg)
  have hcA : Continuous fun M : Matrix (Fin d.n) (Fin d.n) (AE F E) => M.map (cA σ) :=
    continuous_id.matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
  have hA := continuous_aB_k (σ := σ) L δ
  have hc : Continuous (cMF_k (σ := σ) L δ) :=
    Continuous.matrix_fromBlocks hU hA continuous_const (hcA.comp hUn.matrix_transpose)
  have hc' : Continuous (cMF'_k (σ := σ) L δ) :=
    Continuous.matrix_fromBlocks hUn ((hUn.matrix_mul hA).matrix_mul (hcA.comp hU.matrix_transpose)).neg
      continuous_const (hcA.comp hU.matrix_transpose)
  have h1 : Continuous fun c => incM F d.b.1 * cMF_k L δ c * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have h2 : Continuous fun c => incM F d.b.1 * cMF'_k L δ c * incM F (d.b⁻¹).1 :=
    (continuous_const.matrix_mul hc').matrix_mul continuous_const
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine h1.congr fun c => ?_
    show _ = mat2 (cM c)
    rw [kunf.matrix_eq_inFrame_conj d.b, hF c]
  · refine h2.congr fun c => ?_
    show _ = mat2 (cM c)⁻¹
    rw [kunf.matrix_eq_inFrame_conj d.b, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hF c,
      Matrix.inv_eq_right_inv (cMF_mul_k L δ c)]
end PositivityTheory.SiegelWeilFormula.Act.C5

section
set_option linter.unusedSectionVars false
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD_k σ} {R : RD_k d} {L : LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem fix_mul_k {x y : d.G}
    (hx : ∀ k,
      inFrame d.b x k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (hy : ∀ k,
      inFrame d.b y k (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀))
    (k) : inFrame d.b (x * y) k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) := by
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
  simp only [hy]
  rw [← Matrix.mul_apply, Matrix.mul_one, hx]
theorem perF_k (h : Hyp_k L nb uM nb' w₁ cM δ) (Ψ : d.G → ℂ) (hΨ : ∀ r
  ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g)
    (T : nF σ d.Y d.b) (x : d.G) (γ : nA σ d.Y d.b) (hγ : γ ∈ nF σ d.Y d.b) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Ψ (nb (γ + β) * (uM u * x)) * th_k T (γ + β) = Ψ (nb β * (uM u *
      x)) * th_k T β := by
  have e2 : ((γ + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = γ.1 + β.1 := rfl
  rw [kunf.nb_add h.nb, mul_assoc,
    hΨ _ (kunf.nb_rat h.nb hγ) (fix_nb_k h γ)]
  congr 1
  unfold th_k
  rw [e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    kunf.psi_rat d.ok.good.std T ⟨γ, hγ⟩, inv_one, one_mul]
theorem perFE_k (h : Hyp_k L nb uM nb' w₁ cM δ) (Ψ : d.G → ℝ≥0∞) (hΨ :
  ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g, Ψ (r * g) = Ψ g)
    (T : nF σ d.Y d.b) (x : d.G) (γ : nA σ d.Y d.b) (hγ : γ ∈ nF σ d.Y d.b) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Ψ (nb (γ + β) * (uM u * x)) * ‖th_k T (γ + β)‖ₑ = Ψ (nb β * (uM u *
      x)) * ‖th_k T β‖ₑ := by
  have e2 : ((γ + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = γ.1 + β.1 := rfl
  rw [kunf.nb_add h.nb, mul_assoc,
    hΨ _ (kunf.nb_rat h.nb hγ) (fix_nb_k h γ)]
  congr 2
  unfold th_k
  rw [e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    kunf.psi_rat d.ok.good.std T ⟨γ, hγ⟩, inv_one, one_mul]
theorem shift_eq_k (h : Hyp_k L nb uM nb' w₁ cM δ) (r b u : Fin L.n →
  AE F E) (s a : AF F) :
    sM_k R L (r + b) * cM (u,
      s + a) = (sM_k R L r * cM (0,
      s)) * (sM_k R L b * cM (u, a)) := by
  have e1 : cM (u, s + a) = cM (0, s) * cM (u, a) := by
    rw [cM_split_k h,
      centre_additive h,
      cM_split_k h u a, ← mul_assoc,
      cM_comm_k h, mul_assoc]
  rw [sM_add_k, e1]
  simp only [mul_assoc]
  rw [← mul_assoc (sM_k R L b) (cM (0, s)),
    unipotent_commutes_centre h, mul_assoc]
theorem rr_rat_k (h : Hyp_k L nb uM nb' w₁ cM δ) {r : Fin L.n → AE F E}
  (hr : r ∈ L.ratV) {s : AF F}
    (hs : s ∈ (algebraMap F (AF F)).range) : sM_k R L r * cM (0,
      s) ∈ rat2 σ d.Y :=
  mul_mem (sM_rat_k hr)
    (cM_rat_k h (c := (0, s)) (zero_mem _) hs)
theorem rr_fix_k (h : Hyp_k L nb uM nb' w₁ cM δ) (r : Fin L.n → AE F E)
  (s : AF F) (k) :
    inFrame d.b (sM_k R L r * cM (0, s)) k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀) :=
  fix_mul_k (fix_sM_k r)
    (fix_cM_k h (0, s)) k
theorem pt_eq_k (h : Hyp_k L nb uM nb' w₁ cM δ) (x : d.G) (u : Fin L.n
  → AE F E) (β : nA σ d.Y d.b) :
    nb β * (uM u * x) = sM_k R L
      (pb_k L β + (tau_k L uM nb' δ (u,
      C4.prj_k L β)).1) *
      (cM (u, pa_k L δ β + (tau_k L uM nb' δ (u,
        C4.prj_k L β)).2) * (L.j (nb'
        (C4.prj_k L β)) * x)) := by
  calc nb β * (uM u * x) = (L.j (nb' (C4.prj_k L β)) *
         (sM_k R L
         (pb_k L β) * cM (u,
         pa_k L δ β))) * x := by
        rw [nb_split_k h β]
        simp only [mul_assoc]
        rw [← mul_assoc (cM (0, pa_k L δ β)) (uM u),
          ← cM_comm_k h,
          ← cM_split_k h]
    _ = _ := by rw [move_k h]; simp only [mul_assoc]
instance countable_ratV_k (L : LD_k d) : Countable L.ratV := by
  have := (Module.finBasis ℚ E).equivFun.injective.countable
  have h : ((L.ratV : AddSubgroup (Fin L.n → AE F E)) : Set (Fin L.n → AE F E)).Countable := by
    refine (Set.countable_range (incV F : (Fin L.n → E) → _)).mono fun u hu => ?_
    obtain ⟨v, rfl⟩ := C1.ratV_inc_k hu
    exact ⟨v, rfl⟩
  exact h.to_subtype
theorem coordsC_ck_k (h : Hyp_k L nb uM nb' w₁ cM δ) {lam : Measure (nA
  σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β,
      P β = ((pb_k L β,
      pa_k L δ β),
      C4.prj_k L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℂ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g,
        Ψ (r * g) = Ψ g) (x : d.G) :
    ∫ p, Ψ (nb p.2 * (uM p.1 * x)) * th_k T p.2 ∂((ν.restrict 𝓤).prod
      (lam.restrict 𝓖)) =
      c.toReal • ∫ p, Ψ (sM_k R L p.2.2.1 * (cM (p.2.1,
        p.2.2.2) * (L.j (nb' p.1) * x))) * th'_k T' p.1
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  have : Fact (IsFrame2 σ d.Y d.b) := ⟨d.ok.frame⟩
  have : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  have : lam.IsAddHaarMeasure := hc.2.1
  have : lam'.IsAddHaarMeasure := hc'.2.1
  have : ν.IsAddHaarMeasure := hU.2.1
  obtain ⟨-, -, hiff⟩ := pEquiv_k h
  let PM : (nA σ d.Y d.b) ≃ᵐ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) := P.toHomeomorph.toMeasurableEquiv
  have hPM : ∀ β, PM β = ((pb_k L β,
    pa_k L δ β),
    C4.prj_k L β) := hP
  have hPc' : lam.map PM = c • ((ν.prod (lamA F)).prod lam') := hPc
  have hZ : IsAddFundamentalDomain (L.ratV.prod (fA F)) (𝓤 ×ˢ 𝓐) (ν.prod (lamA F)) := fd_prod' hU.2.2.1 h𝓐
  have key := chainC (νu := ν.restrict 𝓤) (ΓN := nF σ d.Y d.b) (ΓZ := L.ratV.prod (fA F)) (ΓN' := nF σ L.Y L.b)
    hPc' (fun a b => map_add P a b) (fun β => by rw [hPM, hiff, AddSubgroup.mem_prod]) hc.2.2.1 hZ hc'.2.2.1
    (continuous_tau_k h).measurable
    (fun p => Ψ (nb p.2 * (uM p.1 * x)) * th_k T p.2)
    (fun q => Ψ (sM_k R L q.2.2.1 * (cM (q.2.1,
      q.2.2.2) * (L.j (nb' q.1) * x))) * th'_k T' q.1)
    (fun γ hγ u β => perF_k h Ψ hΨ T x γ hγ u β)
    (fun g hg w => by
      obtain ⟨hg1, hg2⟩ := AddSubgroup.mem_prod.1 hg
      obtain ⟨β'', u, b, a⟩ := w
      show Ψ (sM_k R L (g.1 + b) * (cM (u,
        g.2 + a) * _)) * _ = Ψ (sM_k R L b * (cM (u, a) * _)) * _
      rw [← mul_assoc, shift_eq_k h, mul_assoc (sM_k R L g.1 * cM (0,
        g.2)), hΨ _ (rr_rat_k h hg1 hg2) (rr_fix_k h g.1 g.2)]
      simp only [mul_assoc])
    (fun u β => by
      rw [hPM]
      show Ψ (nb β * (uM u * x)) * th_k T β = Ψ
        (sM_k R L
        (pb_k L β + (tau_k L uM nb' δ (u,
        C4.prj_k L β)).1) *
        (cM (u, pa_k L δ β + (tau_k L uM nb' δ (u,
          C4.prj_k L β)).2) * (L.j (nb'
          (C4.prj_k L β)) * x))) *
          th'_k T'
          (C4.prj_k L β)
      rw [pt_eq_k (R := R) h x u β]
      congr 1
      unfold th_k
        th'_k
      rw [C4.tr_sub_k L hT β])
  rw [key, ← Measure.prod_restrict]
theorem coordsE_ck_k (h : Hyp_k L nb uM nb' w₁ cM δ) {lam : Measure (nA
  σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β,
      P β = ((pb_k L β,
      pa_k L δ β),
      C4.prj_k L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℝ≥0∞) (_hΨm : Measurable Ψ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g,
        Ψ (r * g) = Ψ g) (x : d.G) :
    ∫⁻ p,
      Ψ (nb p.2 * (uM p.1 * x)) * ‖th_k T p.2‖ₑ ∂((ν.restrict 𝓤).prod
      (lam.restrict 𝓖)) =
      c * ∫⁻ p, Ψ (sM_k R L p.2.2.1 * (cM (p.2.1,
        p.2.2.2) * (L.j (nb' p.1) * x))) * ‖th'_k T' p.1‖ₑ
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) := by
  have : Fact (IsFrame2 σ d.Y d.b) := ⟨d.ok.frame⟩
  have : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  have : lam.IsAddHaarMeasure := hc.2.1
  have : lam'.IsAddHaarMeasure := hc'.2.1
  have : ν.IsAddHaarMeasure := hU.2.1
  obtain ⟨-, -, hiff⟩ := pEquiv_k h
  let PM : (nA σ d.Y d.b) ≃ᵐ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b) := P.toHomeomorph.toMeasurableEquiv
  have hPM : ∀ β, PM β = ((pb_k L β,
    pa_k L δ β),
    C4.prj_k L β) := hP
  have hPc' : lam.map PM = c • ((ν.prod (lamA F)).prod lam') := hPc
  have hZ : IsAddFundamentalDomain (L.ratV.prod (fA F)) (𝓤 ×ˢ 𝓐) (ν.prod (lamA F)) := fd_prod' hU.2.2.1 h𝓐
  have key := chainE (νu := ν.restrict 𝓤) (ΓN := nF σ d.Y d.b) (ΓZ := L.ratV.prod (fA F)) (ΓN' := nF σ L.Y L.b)
    hPc' (fun a b => map_add P a b) (fun β => by rw [hPM, hiff, AddSubgroup.mem_prod]) hc.2.2.1 hZ hc'.2.2.1
    (continuous_tau_k h).measurable
    (fun p => Ψ (nb p.2 * (uM p.1 * x)) * ‖th_k T p.2‖ₑ)
    (fun q => Ψ (sM_k R L q.2.2.1 * (cM (q.2.1,
      q.2.2.2) * (L.j (nb' q.1) * x))) * ‖th'_k T' q.1‖ₑ)
    (fun γ hγ u β => perFE_k h Ψ hΨ T x γ hγ u β)
    (fun g hg w => by
      obtain ⟨hg1, hg2⟩ := AddSubgroup.mem_prod.1 hg
      obtain ⟨β'', u, b, a⟩ := w
      show Ψ (sM_k R L (g.1 + b) * (cM (u,
        g.2 + a) * _)) * _ = Ψ (sM_k R L b * (cM (u, a) * _)) * _
      rw [← mul_assoc, shift_eq_k h, mul_assoc (sM_k R L g.1 * cM (0,
        g.2)), hΨ _ (rr_rat_k h hg1 hg2) (rr_fix_k h g.1 g.2)]
      simp only [mul_assoc])
    (fun u β => by
      rw [hPM]
      show Ψ (nb β * (uM u * x)) * ‖th_k T β‖ₑ = Ψ
        (sM_k R L
        (pb_k L β + (tau_k L uM nb' δ (u,
        C4.prj_k L β)).1) *
        (cM (u, pa_k L δ β + (tau_k L uM nb' δ (u,
          C4.prj_k L β)).2) * (L.j (nb'
          (C4.prj_k L β)) * x))) *
          ‖th'_k T'
          (C4.prj_k L β)‖ₑ
      rw [pt_eq_k (R := R) h x u β]
      congr 2
      unfold th_k
        th'_k
      rw [C4.tr_sub_k L hT β])
  rw [key, ← Measure.prod_restrict]
end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK
end
end

section
open scoped ENNReal
section
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {d : SD_k σ} (R : RD_k d) (L : LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem coordsC_k (h : Hyp_k L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((pb_k L β, pa_k L δ β),
      C4.prj_k L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℂ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g,
        Ψ (r * g) = Ψ g) (x : d.G) :
    ∫ p, Ψ (nb p.2 * (uM p.1 * x)) * th_k T p.2 ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c.toReal • ∫ p, Ψ (sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * th'_k T' p.1
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) :=
          CoordK.coordsC_ck_k h hc hU hc' hT h𝓐 hP hPc Ψ hΨ x
theorem coordsE_k (h : Hyp_k L nb uM nb' w₁ cM δ) {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (Y := d.Y) d.b nb lam 𝓖) {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)}
    (hU : L.UData uM ν 𝓤) {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F))
    {P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)} (hP : ∀ β, P β = ((pb_k L β, pa_k L δ β),
      C4.prj_k L β))
    {c : ℝ≥0∞} (hPc : lam.map P = c • ((ν.prod (lamA F)).prod lam'))
    (Ψ : d.G → ℝ≥0∞) (hΨm : Measurable Ψ) (hΨ : ∀ r ∈ rat2 σ d.Y, (∀ k, inFrame d.b r k (Sum.inl L.i₀) =
      (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) k (Sum.inl L.i₀)) → ∀ g,
        Ψ (r * g) = Ψ g) (x : d.G) :
    ∫⁻ p, Ψ (nb p.2 * (uM p.1 * x)) * ‖th_k T p.2‖ₑ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) =
      c * ∫⁻ p, Ψ (sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * ‖th'_k T' p.1‖ₑ
        ∂((lam'.restrict 𝓖').prod ((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)))) :=
          CoordK.coordsE_ck_k h hc hU hc' hT h𝓐 hP hPc Ψ hΨm hΨ x
end PositivityTheory.SiegelWeilFormula.Act.C5
end

section
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {d : SD_k σ} (R : RD_k d) (L : LD_k d)
variable {R L}
theorem continuous_th'_k (T' : nF σ L.Y L.b) : Continuous fun β : nA σ L.Y L.b => th'_k (d := d) T' β :=
  kfour.continuous_chr (Y := L.Y) (b := L.b) d.ok.good.std.1 T'.1.1
theorem countable_crat_k : Countable (Crat_k L) := by
  have : Countable L.ratV := by
    have := (Module.finBasis ℚ E).equivFun.injective.countable
    refine Function.Surjective.countable (f := fun v : Fin L.n → E =>
      (⟨incV F v, AddSubgroup.subset_closure ⟨v, rfl⟩⟩ : L.ratV)) fun u => ?_
    obtain ⟨v, hv⟩ := C1.ratV_inc_k u.2
    exact ⟨v, Subtype.ext hv.symm⟩
  have := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable (Set.range (algebraMap F (AF F))) := (Set.countable_range _).to_subtype
  refine Function.Injective.countable (f := fun c : Crat_k L =>
    ((⟨c.1.1, c.2.1⟩ : L.ratV), (⟨c.1.2, c.2.2⟩ : Set.range (algebraMap F (AF F)))))
    fun c c' hcc => ?_
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hcc
  exact Subtype.ext (Prod.ext hcc.1 (congrArg Subtype.val hcc.2))
end PositivityTheory.SiegelWeilFormula.Act.C5
end

section
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {d : SD_k σ} (R : RD_k d) (L : LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G} {cM :
  (Fin L.n → AE F E) × AF F → d.G} {δ : E}
def rationalCosetEquiv (L : LD_k d) : Crat_k L ≃ L.ratV × fA F where
  toFun c := (⟨c.1.1, c.2.1⟩, ⟨c.1.2, c.2.2⟩)
  invFun c := ⟨((c.1 : Fin L.n → AE F E), (c.2 : AF F)), c.1.2, c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem countable_rational_vectors (L : LD_k d) : Countable L.ratV := by
  have := (Module.finBasis ℚ E).equivFun.injective.countable
  refine Function.Surjective.countable (f := fun v : Fin L.n → E =>
    (⟨incV F v, AddSubgroup.subset_closure ⟨v, rfl⟩⟩ : L.ratV)) fun u => ?_
  obtain ⟨v, hv⟩ := C1.ratV_inc_k u.2
  exact ⟨v, Subtype.ext hv.symm⟩
theorem coset_point_decomposition (h : Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z :
  ℂ) {γ' : G2 σ L.Y}
    {Λ : ((Fin L.n → AE F E) × (Fin L.n → AE F E)) ≃ₜ+ ((Fin L.n → AE F E) × (Fin L.n → AE F E))}
    {Q : (Fin L.n → AE F E) × (Fin L.n → AE F E) → AF F}
    (hΛ : ∀ b u a, L.j γ' * (sM_k R L b * cM (u, a)) = sM_k R L (Λ (b, u)).1 * cM ((Λ (b, u)).2, a + Q (b, u)) * L.j γ')
    {Z : (Fin L.n → AE F E) → (Fin L.n → AE F E) → AF F}
    (hZ : ∀ u₀ a₀ b u a, cM (u₀, a₀) * (sM_k R L b * cM (u, a)) = sM_k R L b * cM (u₀ + u, a₀ + a + Z u₀ b))
    (Y : d.G) (c₀ : (Fin L.n → AE F E) × AF F) (p : (Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) :
    phz_k d f s₁ z (w₁ * (cM c₀ * (L.j γ' * (sM_k R L p.2.1 * (cM (p.1,
      p.2.2) * Y))))) =
      phz_k d f s₁ z (w₁ * (cM (UnfoldingIntegralSum.sh Λ Q Z c₀ p) * (L.j
        γ' * Y))) := by
  obtain ⟨u₀, a₀⟩ := c₀
  obtain ⟨u, b, a⟩ := p
  have e1 : L.j γ' * (sM_k R L b * (cM (u, a) * Y)) = (L.j γ' * (sM_k R L b * cM (u,
    a))) * Y := by simp only [mul_assoc]
  have e2 : ∀ c', cM (u₀, a₀) * (sM_k R L (Λ (b, u)).1 * cM c' * L.j γ' * Y) =
      (cM (u₀, a₀) * (sM_k R L (Λ (b, u)).1 * cM c')) * (L.j γ' * Y) := by intro c'; simp only [mul_assoc]
  rw [e1, hΛ, e2, hZ, mul_assoc, section_unipotent_invariant h hf z]
  simp only [UnfoldingIntegralSum.sh, add_assoc]
theorem unfqE_k (h : Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤)
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F)) {γ' : G2 σ L.Y} (hγ : γ' ∈ rat2 σ L.Y) (Y : d.G) :
    ∫⁻ p, ∑' c₀ : Crat_k L,
      ‖phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j γ' * (sM_k R L p.2.1 * (cM
      (p.1, p.2.2) * Y)))))‖ₑ
        ∂((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐))) =
      ∫⁻ c,
        ‖phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y)))‖ₑ ∂(ν.prod (lamA F))
        := by
  obtain ⟨-, hν, hU0, hU1⟩ := hU
  have := hν
  have := countable_rational_vectors L
  obtain ⟨Λ, Q, hQ, hΛeq, hΛrat⟩ := j_conj_k (R := R) h γ'
  obtain ⟨Z, hZ, -, hheis⟩ := heis_k (R := R) h
  have hg : Continuous fun c => phz_k d f s₁ z (w₁ * (cM c * (L.j γ' *
    Y))) :=
    (ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z).comp (continuous_const.mul ((continuous_cM_k
      h).mul continuous_const))
  rw [← UnfoldingIntegralSum.unf_lint hU0 hU1 (fd_prod hU0 hU0) h𝓐 Λ (hΛrat hγ) hQ.measurable hZ.measurable
    hg.measurable.eNorm]
  refine lintegral_congr fun p => ?_
  rw [← (rationalCosetEquiv L).symm.tsum_eq]
  exact tsum_congr fun c => by rw [coset_point_decomposition h hf z hΛeq hheis]; rfl
theorem unfqC_k (h : Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤)
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F)) {γ' : G2 σ L.Y} (hγ : γ' ∈ rat2 σ L.Y) (Y : d.G)
    (hfin : ∫⁻ c,
      ‖phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y)))‖ₑ ∂(ν.prod (lamA F)) <
      ⊤) :
    ∫ p, ∑' c₀ : Crat_k L,
      phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j γ' * (sM_k R L p.2.1 * (cM
      (p.1, p.2.2) * Y)))))
        ∂((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐))) =
      ∫ c, phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y))) ∂(ν.prod (lamA F))
        := by
  obtain ⟨-, hν, hU0, hU1⟩ := hU
  have := hν
  have := countable_rational_vectors L
  obtain ⟨Λ, Q, hQ, hΛeq, hΛrat⟩ := j_conj_k (R := R) h γ'
  obtain ⟨Z, hZ, -, hheis⟩ := heis_k (R := R) h
  have hg : Continuous fun c => phz_k d f s₁ z (w₁ * (cM c * (L.j γ' *
    Y))) :=
    (ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z).comp (continuous_const.mul ((continuous_cM_k
      h).mul continuous_const))
  rw [← UnfoldingIntegralSum.unf_int hU0 hU1 (fd_prod hU0 hU0) h𝓐 Λ (hΛrat hγ) hQ.measurable hZ.measurable hg.measurable
    hfin]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  beta_reduce
  rw [← (rationalCosetEquiv L).symm.tsum_eq]
  exact tsum_congr fun c => by rw [coset_point_decomposition h hf z hΛeq hheis]; rfl
end PositivityTheory.SiegelWeilFormula.Act.C5
end

section
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {d : SD_k σ} (R : RD_k d) (L : LD_k d)
variable {R L}
theorem unf_k (R : RD_k d) {f : d.G → ℂ} {s₁ : ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖)
    {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤)
    {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    {nb' : nA σ L.Y L.b → G2 σ L.Y} {lam' : Measure (nA σ L.Y L.b)} {𝓖' : Set (nA σ L.Y L.b)}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖')
    (habs : ∀ x, (∀ q : Cs_k d,
      Integrable (kq_k L f s₁ z nb T uM
      (rep_k q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖))) ∧
      Summable fun q : Cs_k d => ∫ p,
        ‖kq_k L f s₁ z nb T uM
        (rep_k q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    {w₁ : d.G} {cM : (Fin L.n → AE F E) × AF F → d.G} {κ : Measure ((Fin L.n → AE F E) × AF F)} {δ : E}
    (h : Hyp_k L nb uM nb' w₁ cM δ) (hcM : Continuous cM) (hκ : κ.IsAddHaarMeasure) :
    ∃ K : ℂ, ∀ x,
      secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 x = K * ∑' q' :
      Cs_k L.sd, ∫ β in 𝓖',
      (∫ c,
        phz_k d f s₁ z (w₁ * (cM c * (L.j
        (rep_k q' * nb' β) * x))) ∂κ) * th'_k (d := d) T' β ∂lam' := by
  classical
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (Cs_k d) := Quotient.countable
  have : Countable (rat2 σ L.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ L.Y
  have : Countable (Cs_k L.sd) := Quotient.countable
  have : Countable (Crat_k L) := countable_crat_k
  have : ν.IsAddHaarMeasure := hU.2.1
  have : lam.IsAddHaarMeasure := hc.2.1
  have : lam'.IsAddHaarMeasure := hc'.2.1
  have hψc : Continuous d.B.ψ := d.ok.good.std.1
  obtain ⟨P, hP, -⟩ := pEquiv_k h
  obtain ⟨cP, hcP0, hcPt, hPc⟩ := @lam_map_k _ _ _ _ _ _ _ _ d L lam hc.2.1 ν hU.2.1 lam' hc'.2.1 P
  obtain ⟨cK, hcK0, hcKt, hκeq⟩ := kap_eq_k (ν := ν) (κ := κ)
  obtain ⟨𝓐, h𝓐, h𝓐0, h𝓐t⟩ := exists_fd_fA (F := F)
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hU.2.2.2])
  have : IsFiniteMeasure (lam'.restrict 𝓖') := isFiniteMeasure_restrict.2 (by erw [hc'.2.2.2]; exact ENNReal.one_ne_top)
  have : IsFiniteMeasure ((lamA F).restrict 𝓐) := isFiniteMeasure_restrict.2 h𝓐t
  obtain ⟨e, he⟩ := second_orbit_bijection h
  refine ⟨(cP.toReal : ℂ) * ((cK.toReal : ℂ))⁻¹, fun x => ?_⟩
  have hΦc : Continuous (phz_k d f s₁ z) :=
    ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z
  obtain ⟨hi, hs⟩ := habs x
  obtain ⟨e1, fin1⟩ := second_orbit_section_integral (L := L) (nb := nb) (uM := uM) hU.2.2.2 hc.2.2.2 x hi hs
  have e2 := coordsC_k (R := R) h hc hU hc' hT h𝓐 hP hPc (eisensteinSecondTerm L
    (phz_k d f s₁ z)) (fun r hr hx g => eisenstein_term_left_invariant hf
    z hr hx g) x
  set μO := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμO
  set μI := (ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐)) with hμI
  set μN := (lam'.restrict 𝓖').prod μI with hμN
  have hnb' : Continuous nb' := kunf.continuous_nb hc'.1
  have hnew : Continuous fun p : nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) =>
      sM_k R L p.2.2.1 * (cM (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x)) := by
    refine ((continuous_sM'_k (R := R) (L := L)).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).mul
      ((hcM.comp ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp (continuous_snd.comp
        continuous_snd)))).mul
        (((L.cont.comp (hnb'.comp continuous_fst))).mul continuous_const))
  have hth' : Continuous fun β : nA σ L.Y L.b => th'_k (d := d) T' β := continuous_th'_k T'
  let G : (Σ _ : Cs_k L.sd,
    Crat_k L) → nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) → ℂ :=
    fun y p => phz_k d f s₁ z (w₁ * (cM y.2.1 * (L.j
      (rep_k y.1) * (sM_k R L p.2.2.1 * (cM (p.2.1,
      p.2.2.2) * (L.j (nb' p.1) * x)))))) *
      th'_k (d := d) T' p.1
  have hGc : ∀ y, Continuous (G y) := fun y =>
    (hΦc.comp (continuous_const.mul (continuous_const.mul (continuous_const.mul hnew)))).mul (hth'.comp continuous_fst)
  have : BorelSpace (GL (Fin d.n ⊕ Fin d.n) (AE F E)) := GlobalTheory.EisBL.Borel.borelGL
  have : BorelSpace d.G := Subtype.borelSpace _
  have fin2 : ∫⁻ p, ∑' y, ‖G y p‖ₑ ∂μN < ⊤ := by
    have hE := coordsE_k (R := R) h hc hU hc' hT h𝓐 hP hPc
      (fun g => ∑' q : {q : Cs_k d // ¬
        FirstOrbit L (rep_k
        q)},
        ‖phz_k d f s₁ z
        (rep_k q.1 * g)‖ₑ)
      (Measurable.tsum fun q => (hΦc.comp (continuous_const.mul continuous_id)).eNorm.measurable)
      (fun r hr hx g => eisenstein_norm_sum_invariant hf z hr hx g) x
    have l1 : ∫⁻ p,
      (∑' q : {q : Cs_k d // ¬
      FirstOrbit L (rep_k
      q)},
      ‖phz_k d f s₁ z (rep_k
      q.1 * (nb p.2 * (uM p.1 * x)))‖ₑ) *
        ‖th_k T p.2‖ₑ ∂μO < ⊤ := by
      refine lt_of_eq_of_lt ?_ fin1
      refine lintegral_congr fun p => ?_
      rw [← ENNReal.tsum_mul_right]
      exact tsum_congr fun q => (eNorm_mul _ _).symm
    rw [hE] at l1
    have l2 : ∫⁻ p,
      (∑' q : {q : Cs_k d // ¬
      FirstOrbit L (rep_k
      q)},
        ‖phz_k d f s₁ z
          (rep_k q.1 * (sM_k R L p.2.2.1 * (cM (p.2.1,
          p.2.2.2) * (L.j (nb' p.1) * x))))‖ₑ) * ‖th'_k (d := d) T' p.1‖ₑ
        ∂μN < ⊤ := by
      by_contra hcon
      rw [not_lt, top_le_iff] at hcon
      rw [hcon, ENNReal.mul_top hcP0] at l1
      exact lt_irrefl _ l1
    refine lt_of_eq_of_lt (lintegral_congr fun p => ?_) l2
    rw [(eisenstein_second_term_expand h hf z he _).2, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun y => eNorm_mul _ _
  have hGm : ∀ y, AEMeasurable (fun p => ‖G y p‖ₑ) μN := fun y => (hGc y).eNorm.measurable.aemeasurable
  have hGlt : ∀ y, ∫⁻ p, ‖G y p‖ₑ ∂μN < ⊤ := fun y =>
    lt_of_le_of_lt (lintegral_mono fun p => le_tsum (f := fun y => ‖G y p‖ₑ) y) fin2
  have hGi : ∀ y, Integrable (G y) μN := fun y => ⟨(hGc y).aestronglyMeasurable, hGlt y⟩
  have hGs : Summable fun y => ∫ p, ‖G y p‖ ∂μN := by
    have h1 : ∀ y, ∫ p, ‖G y p‖ ∂μN = (∫⁻ p, ‖G y p‖ₑ ∂μN).toReal := fun y =>
      integral_norm_eq_lintegral_eNorm (hGi y).aestronglyMeasurable
    simp_rw [h1]
    refine ENNReal.summable_toReal ?_
    rw [← lintegral_tsum hGm]
    exact fin2.ne
  have e3 : ∫ p,
    eisensteinSecondTerm L (phz_k d f s₁ z) (sM_k R L p.2.2.1 * (cM
    (p.2.1, p.2.2.2) * (L.j (nb' p.1) * x))) * th'_k (d := d) T' p.1 ∂μN =
      ∑' y, ∫ p, G y p ∂μN := by
    rw [(hasSum_integral_of_summable_integral_norm hGi hGs).tsum_eq]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [G]
    rw [(eisenstein_second_term_expand h hf z he _).1, tsum_mul_right]
  have hsI : Summable fun y => ∫ p, G y p ∂μN := hGs.of_norm_bounded (fun y => norm_integral_le_integral_norm _)
  rw [hsI.tsum_sigma] at e3
  have hκ' : ∀ g : (Fin L.n → AE F E) × AF F → ℂ, ∫ c, g c ∂(ν.prod (lamA F)) = ((cK.toReal : ℂ))⁻¹ * ∫ c, g c ∂κ := by
    intro g
    rw [hκeq, integral_smul_measure, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hcK0, hcKt⟩)
  have e4 : ∀ q' : Cs_k L.sd, ∑' c₀ : Crat_k L, ∫ p, G ⟨q',
    c₀⟩ p ∂μN = ((cK.toReal : ℂ))⁻¹ *
      ∫ β in 𝓖', (∫ c,
        phz_k d f s₁ z (w₁ * (cM c * (L.j
        (rep_k q' * nb' β) * x))) ∂κ) * th'_k (d := d) T' β ∂lam' := by
    intro q'
    have hi' : ∀ c₀ : Crat_k L, Integrable (G ⟨q', c₀⟩) μN := fun c₀ => hGi _
    have hs' : Summable fun c₀ : Crat_k L => ∫ p, ‖G ⟨q', c₀⟩ p‖ ∂μN := hGs.sigma_factor q'
    obtain ⟨-,
      hex⟩ := exch (μ := lam'.restrict 𝓖') (m := μI) (fun c₀ : Crat_k L => G ⟨q',
      c₀⟩) hi' hs'
    have hpr : ∀ c₀ : Crat_k L, ∫ p, G ⟨q', c₀⟩ p ∂μN = ∫ β, ∫ v, G ⟨q', c₀⟩ (β, v) ∂μI ∂(lam'.restrict 𝓖') :=
      fun c₀ => integral_prod _ (hi' c₀)
    simp_rw [hpr]
    rw [← hex, ← integral_const_mul]
    refine integral_congr_ae ?_
    have hmq : Measurable fun p : nA σ L.Y L.b × ((Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) =>
        ∑' c₀ : Crat_k L, ‖G ⟨q', c₀⟩ p‖ₑ := Measurable.tsum fun c₀ => (hGc _).eNorm.measurable
    have hfinq : ∫⁻ p, ∑' c₀ : Crat_k L, ‖G ⟨q', c₀⟩ p‖ₑ ∂μN < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono fun p => ?_) fin2
      exact (le_tsum (f := fun q'' => ∑' c₀ : Crat_k L, ‖G ⟨q'', c₀⟩ p‖ₑ) q').trans
        (tsum_sigma' (fun y => ‖G y p‖ₑ)).symm.le
    rw [hμN, lintegral_prod _ hmq.aemeasurable] at hfinq
    have hae := ae_lt_top (hmq.lintegral_prod_right') hfinq.ne
    filter_upwards [hae] with β hβ
    have hG' : ∀ v, ∑' c₀ : Crat_k L, G ⟨q', c₀⟩ (β, v) = (∑' c₀ : Crat_k L,
        phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j
          (rep_k q') * (sM_k R L v.2.1 * (cM (v.1,
          v.2.2) * (L.j (nb' β) * x))))))) *
          th'_k (d := d) T' β := fun v => by simp only [G]; rw [tsum_mul_right]
    simp_rw [hG']
    rw [integral_mul_const]
    have hjj : L.j (rep_k q') * (L.j (nb' β) * x) = L.j
      (rep_k q' * nb' β) * x := by rw [map_mul, mul_assoc]
    by_cases hθ : th'_k (d := d) T' β = 0
    · rw [hθ, mul_zero, mul_zero, mul_zero]
    · have hθe : ‖th'_k (d := d) T' β‖ₑ ≠ 0 := eNorm_ne_zero.2 hθ
      have hl : ∫⁻ v, ∑' c₀ : Crat_k L,
          ‖phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j
            (rep_k q') * (sM_k R L v.2.1 * (cM (v.1,
            v.2.2) * (L.j (nb' β) * x))))))‖ₑ ∂μI < ⊤ := by
        have e5 : ∫⁻ v, ∑' c₀ : Crat_k L, ‖G ⟨q', c₀⟩ (β, v)‖ₑ ∂μI = (∫⁻ v, ∑' c₀ : Crat_k L,
            ‖phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j
              (rep_k q') * (sM_k R L v.2.1 * (cM (v.1,
              v.2.2) * (L.j (nb' β) * x))))))‖ₑ ∂μI) *
              ‖th'_k (d := d) T' β‖ₑ := by
          rw [← lintegral_mul_const' _ _ eNorm_ne_top]
          refine lintegral_congr fun v => ?_
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun c₀ => eNorm_mul _ _
        rw [e5] at hβ
        by_contra hcon
        rw [not_lt, top_le_iff] at hcon
        rw [hcon, ENNReal.top_mul hθe] at hβ
        exact lt_irrefl _ hβ
      have hγ : rep_k q' ∈ rat2 σ L.Y := (Quot.out q').2
      rw [unfqE_k h hf z hU h𝓐 hγ (L.j (nb' β) * x)] at hl
      rw [unfqC_k h hf z hU h𝓐 hγ (L.j (nb' β) * x) hl, hκ']
      simp_rw [hjj]
      ring
  rw [e1]; erw [e2, e3]
  simp_rw [e4]
  rw [tsum_mul_left, Complex.real_smul]
  ring
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

namespace GlobalTheory.ThetaQuasiRatCM
theorem thetaTr_ratWF_add_quasi_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ
  : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
            thetaTr F co B.ψ φ (Formalism.IndefR.DatumF.ratWF γ + w) =
              B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) *
                thetaTr F co B.ψ φ w := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hξ hψ JA JB ξ hA hJB κ _ co hrat φ hφ γ w
  exact GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add_k F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hξ JA JB ξ hA hJB κ
    co hrat φ hφ γ w
end GlobalTheory.ThetaQuasiRatCM
