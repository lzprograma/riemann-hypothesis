module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.BumpLat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGDecomp
public import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariant
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.EqAdeleSupportedAtFinitePlaceOfSupportedAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Prelims.LatticeOrderExistsInverseOneAddUniformizerSmul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Prelims.MemNhdsOneOfCongruenceLatticeOrder
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Prelims.UnitaryLatticeExistsFrame
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.FinSplit
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.CompFinLiftE
public import Development.WeilBound.ThetaLifts.LatticeBasics.LocMeas
public import Development.WeilBound.ThetaLifts.LatticeBasics.MemLam
public import GroundTheory.GlobalFields.CompletionAtPlace.Integers

/-! # TPGBumpAny: Consolidated global theta-kernel definitions and proofs (TPGBumpAny). -/
@[expose] public section

open UpperTheory.TP.W (GoodK)

open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open AddChar (map_add_eq_mul)
open GlobalTheory.ThK.Dbl (locGrp)

section
open scoped TensorProduct
open UpperTheory.TP.BA hiding sg
open PositivityTheory.ThKH.Iwas GlobalTheory.LFun GlobalTheory.LFun.InertChart Formalism.UG PositivityTheory.ThK
open Matrix (vecMulVec vecMulVec_apply)

noncomputable section
namespace UpperTheory.LatD

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} {v : Pl F}

omit [NumberField E] in
private theorem at_self_pk {M : Type} [AddCommGroup M] [Module (AF F) M] {x : M} (hx : At (evFin F v) x) :
    sg v 1 • x = x := by
  have h1 := hx (1 - sg v 1) (by rw [map_sub, map_one, ev_sg, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1; exact h1.symm

omit [NumberField E] in
private theorem at_mulA_pk {a : AF F} (ha : At (evFin F v) a) (a' : AF F) : At (evFin F v) (a * a') := fun u hu => by
  have h := ha u hu; rw [smul_eq_mul] at h ⊢; rw [← mul_assoc, h, zero_mul]

private theorem sgE_mem_Oh_pk {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) : sgE E v y ∈ Oh E v := by
  refine intLoc_induction (p := fun y => sgE E v y ∈ Oh E v) (fun a ha x => ?_)
    (by rw [map_zero]; exact zero_mem _) (fun _ _ hy hz => by rw [map_add]; exact add_mem hy hz)
    (fun _ hy => by rw [map_neg]; exact neg_mem hy) hy
  refine AddSubgroup.subset_closure ⟨sg v a, at_sg a, by rwa [ev_sg], x, ?_⟩
  change (sg v a) ⊗ₜ[F] (x : E) = (sg v a * 1) ⊗ₜ[F] (x : E); rw [mul_one]

private theorem mem_Oh_pk {x : AE F E} (hx : At (evFin F v) x) (h : compFin F E v x ∈ intLoc F E v) : x ∈ Oh E v := by
  rw [← at_self_pk hx, ← sgE_comp]; exact sgE_mem_Oh_pk h

omit [NumberField E] in
private theorem at_eM_pk (m : ℕ) : At (evFin F v) (eM (E := E) v m) := fun u hu => by
  change u • (sg v 1 • (1 : Matrix (Fin m) (Fin m) (AE F E))) = 0
  rw [smul_smul, ← smul_eq_mul, at_sg 1 u hu, zero_smul]

omit [NumberField E] in
private theorem mul_eM_pk {M : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evFin F v) M) : M * eM v n = M := by
  rw [Matrix.mul_smul, Matrix.mul_one]; exact at_self_pk h

omit [NumberField E] in
private theorem eM_mul_pk {M : Matrix (Fin n) (Fin n) (AE F E)} (h : At (evFin F v) M) : eM v n * M = M := by
  rw [Matrix.smul_mul, Matrix.one_mul]; exact at_self_pk h

private theorem oh_ind_pk {p : AE F E → Prop}
    (gen : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ o : 𝓞 E,
      p (a • inclR (AF F) (o : E)))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x, p x → p (-x)) {x : AE F E} (hx : x ∈ Oh E v) :
    p x :=
  AddSubgroup.closure_induction (p := fun x _ => p x) (by rintro _ ⟨a, h1, h2, o, rfl⟩; exact gen a h1 h2 o)
    zero (fun x y _ _ => add x y) (fun x _ => neg x) hx

private theorem oh_mul_pk {x y : AE F E} (hx : x ∈ Oh E v) (hy : y ∈ Oh E v) : x * y ∈ Oh E v := by
  refine oh_ind_pk (p := fun x => x * y ∈ Oh E v) (fun a h1 h2 o => ?_) (by simp [zero_mem])
    (fun _ _ h h' => by rw [add_mul]; exact add_mem h h') (fun _ h => by rw [neg_mul]; exact neg_mem h) hx
  refine oh_ind_pk (p := fun y => a • inclR (AF F) (o : E) * y ∈ Oh E v) (fun a' h1' h2' o' => ?_)
    (by simp [zero_mem]) (fun _ _ h h' => by rw [mul_add]; exact add_mem h h')
    (fun _ h => by rw [mul_neg]; exact neg_mem h) hy
  have e : a • inclR (F := F) (AF F) (o : E) * a' • inclR (F := F) (AF F) (o' : E) =
      (a * a') • inclR (F := F) (AF F) ((o * o' : 𝓞 E) : E) := by rw [smul_mul_smul_comm, ← map_mul]; rfl
  rw [e]
  exact AddSubgroup.subset_closure ⟨a * a', at_mulA_pk h1 a', by rw [map_mul]; exact mul_mem h2 h2', o * o', rfl⟩

private theorem oh_sg_pk {t : Fv F v} (ht : t ∈ v.adicCompletionIntegers F) : sg v t • (1 : AE F E) ∈ Oh E v := by
  have h : sg v t • inclR (AF F) ((1 : 𝓞 E) : E) ∈ Oh E v :=
    AddSubgroup.subset_closure ⟨sg v t, at_sg t, by rwa [ev_sg], 1, rfl⟩
  simpa using h

private theorem oh_smul_pk {t : Fv F v} (ht : t ∈ v.adicCompletionIntegers F) {x : AE F E} (hx : x ∈ Oh E v) :
    sg v t • x ∈ Oh E v := by
  have := oh_mul_pk (oh_sg_pk ht) hx; rwa [smul_mul_assoc, one_mul] at this

omit [NumberField E] in
private theorem lat_ind_pk {m : ℕ} {X : Spc F E m} {p : (Fin m → AE F E) → Prop}
    (gen : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ y ∈ X.L,
      p (fun i => a • inclR (AF F) (y i)))
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y)) (neg : ∀ x, p x → p (-x)) {x : Fin m → AE F E}
    (hx : x ∈ latW X v) : p x :=
  AddSubgroup.closure_induction (p := fun x _ => p x) (by rintro _ ⟨a, h1, h2, y, hy, rfl⟩; exact gen a h1 h2 y hy)
    zero (fun x y _ _ => add x y) (fun x _ => neg x) hx

private theorem lat_smul_pk {m : ℕ} {X : Spc F E m} {o : AE F E} (ho : o ∈ Oh E v) {z : Fin m → AE F E}
    (hz : z ∈ latW X v) : (fun i => o * z i) ∈ latW X v := by
  refine oh_ind_pk (p := fun o => (fun i => o * z i) ∈ latW X v) (fun a h1 h2 o => ?_)
    (by simp only [zero_mul]; exact zero_mem _) (fun _ _ h h' => by simp only [add_mul]; exact add_mem h h')
    (fun _ h => by simp only [neg_mul]; exact neg_mem h) ho
  refine lat_ind_pk (p := fun z => (fun i => a • inclR (AF F) (o : E) * z i) ∈ latW X v)
    (fun a' h1' h2' y hy => ?_)
    (by simp only [Pi.zero_apply, mul_zero]; exact zero_mem _)
    (fun _ _ h h' => by simp only [Pi.add_apply, mul_add]; exact add_mem h h')
    (fun _ h => by simp only [Pi.neg_apply, mul_neg]; exact neg_mem h) hz
  refine AddSubgroup.subset_closure ⟨a * a', at_mulA_pk h1 a', by rw [map_mul]; exact mul_mem h2 h2', o • y,
    X.L.smul_mem o hy, funext fun i => by rw [smul_mul_smul_comm, ← map_mul]; rfl⟩

private theorem vmv_mem_pk {X : Spc F E n} {W : Spc F E d} {z : Fin n → AE F E} {y : Fin d → AE F E}
    (hz : z ∈ latW X v) (hy : y ∈ latW W v) : vecMulVec z y ∈ latAtV X W v := by
  refine lat_ind_pk (p := fun z => vecMulVec z y ∈ latAtV X W v) (fun a h1 h2 x hx => ?_)
    (by convert zero_mem (latAtV X W v); ext i j; simp [vecMulVec_apply])
    (fun p q h h' => by convert add_mem h h'; ext i j; simp [vecMulVec_apply, add_mul])
    (fun p h => by convert neg_mem h; ext i j; simp [vecMulVec_apply]) hz
  refine lat_ind_pk (p := fun y => vecMulVec (fun i => a • inclR (AF F) (x i)) y ∈ latAtV X W v)
    (fun a' h1' h2' y hy => AddSubgroup.subset_closure ⟨a * a', at_mulA_pk h1 a', by rw [map_mul]; exact mul_mem h2 h2',
      x, hx, y, hy, by ext i j; simp [vecMulVec_apply, incM]; rw [mul_comm a a', mul_smul]⟩)
    (by convert zero_mem (latAtV X W v); ext i j; simp [vecMulVec_apply])
    (fun p q h h' => by convert add_mem h h'; ext i j; simp [vecMulVec_apply, mul_add])
    (fun p h => by convert neg_mem h; ext i j; simp [vecMulVec_apply]) hy

omit [NumberField E] in
private theorem gam_ind_pk {X : Spc F E n} {W : Spc F E d} {p : Matrix (Fin n) (Fin d) (AE F E) → Prop}
    (gen : ∀ z ∈ latW X v, ∀ y ∈ latW W v, p (vecMulVec z y)) (zero : p 0) (add : ∀ x y, p x → p y → p (x + y))
    (neg : ∀ x, p x → p (-x)) {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) : p γ := by
  refine AddSubgroup.closure_induction (p := fun x _ => p x) ?_ zero (fun x y _ _ => add x y) (fun x _ => neg x) hγ
  rintro _ ⟨a, h1, h2, x, hx, y, hy, rfl⟩
  have e : a • incM F (vecMulVec x y) = vecMulVec (fun i => a • inclR (AF F) (x i))
      (fun j => sg v 1 • inclR (AF F) (y j)) := by
    ext i j
    have e1 : a * sg v 1 = a := by rw [mul_comm]; exact at_self_pk h1
    simp [vecMulVec_apply, incM]; rw [← mul_smul, mul_comm (sg v 1) a, e1]
  rw [e]
  exact gen _ (AddSubgroup.subset_closure ⟨a, h1, h2, x, hx, rfl⟩) _
    (AddSubgroup.subset_closure ⟨sg v 1, at_sg 1, by rw [ev_sg]; exact one_mem _, y, hy, rfl⟩)

private theorem core_pk {A : Type} [CommRing A] (S : Subring A) (s : A →+* A) (hS : ∀ x ∈ S, s x ∈ S)
    (ss : ∀ x, s (s x) = x) {e : A} (he : e ∈ S) (h1 : e + s e = 1) (h2 : e * s e = 0) {n d : ℕ} (hnd : 2 * n ≤ d)
    {Γ G' : Matrix (Fin d) (Fin d) A} (hΓ : ∀ i j, Γ i j ∈ S) (hG' : ∀ i j, G' i j ∈ S) (hi : G' * Γ = 1)
    (hsk : (Γ.map s)ᵀ = -Γ) :
    ∃ (c : Matrix (Fin n) (Fin d) A) (ρ : Matrix (Fin d) (Fin n) A), (∀ i j, c i j ∈ S) ∧ (∀ i j, ρ i j ∈ S) ∧
      c * ρ = 1 ∧ c * Γ * (c.map s)ᵀ = 0 := by
  classical
  let f₁ : Fin n → Fin d := fun i => ⟨i, by omega⟩
  let f₂ : Fin n → Fin d := fun i => ⟨i + n, by omega⟩
  have i₁ : Function.Injective f₁ := fun _ _ h => Fin.ext (by simpa [f₁] using h)
  have i₂ : Function.Injective f₂ := fun _ _ h => Fin.ext (by simpa [f₂] using h)
  have dj : ∀ a b, f₁ a ≠ f₂ b := fun a b h => by have := congrArg Fin.val h; simp only [f₁, f₂] at this; omega
  have key : ∀ f g : Fin n → Fin d, ((1 : Matrix (Fin d) (Fin d) A).submatrix id f)ᵀ *
      (1 : Matrix (Fin d) (Fin d) A).submatrix id g = (1 : Matrix (Fin d) (Fin d) A).submatrix f g := fun f g => by
    rw [Matrix.transpose_submatrix, Matrix.transpose_one, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      Matrix.one_mul]
  let E₁ := (1 : Matrix (Fin d) (Fin d) A).submatrix id f₁
  let E₂ := (1 : Matrix (Fin d) (Fin d) A).submatrix id f₂
  have p11 : E₁ᵀ * E₁ = 1 := by rw [key, Matrix.submatrix_one _ i₁]
  have p22 : E₂ᵀ * E₂ = 1 := by rw [key, Matrix.submatrix_one _ i₂]
  have p12 : E₁ᵀ * E₂ = 0 := by rw [key]; exact Matrix.ext fun a b => Matrix.one_apply_ne (dj a b)
  have p21 : E₂ᵀ * E₁ = 0 := by rw [key]; exact Matrix.ext fun a b => Matrix.one_apply_ne (dj b a).symm
  have intE : ∀ f : Fin n → Fin d, ∀ i j, ((1 : Matrix (Fin d) (Fin d) A).submatrix id f) i j ∈ S := fun f i j => by
    simp only [Matrix.submatrix_apply, id, Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]
  have mapE : ∀ f : Fin n → Fin d, ((1 : Matrix (Fin d) (Fin d) A).submatrix id f).map s =
      (1 : Matrix (Fin d) (Fin d) A).submatrix id f := fun f => Matrix.ext fun i j => by
    simp only [Matrix.map_apply, Matrix.submatrix_apply, id, Matrix.one_apply]; split_ifs <;> simp
  have hΓG : Γ * G' = 1 := mul_eq_one_comm.1 hi
  let T := (G'.map s)ᵀ; let Q := (Γ.map s)ᵀ
  have hTQ : T * Q = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hΓG, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hTΓ : T * Γ = -1 := by rw [← neg_neg (T * Γ), ← Matrix.mul_neg, ← hsk]; exact congrArg Neg.neg hTQ
  have mapT : T.map s = G'ᵀ := Matrix.ext fun i j => by simp [T, ss]
  have he2 : e * e = e := by linear_combination e * h1 - h2
  have hs2 : s e * s e = s e := by linear_combination s e * h1 - h2
  have h2' : s e * e = 0 := by rw [mul_comm, h2]
  refine ⟨e • E₁ᵀ + s e • (E₂ᵀ * T), e • E₁ + s e • (Q * E₂),
    fun i j => add_mem (mul_mem he (intE f₁ j i)) (mul_mem (hS _ he) (by
      rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (intE f₂ k i) (hS _ (hG' j k)))),
    fun i j => add_mem (mul_mem he (intE f₁ i j)) (mul_mem (hS _ he) (by
      rw [Matrix.mul_apply]; exact sum_mem fun k _ => mul_mem (hS _ (hΓ k i)) (intE f₂ k j))), ?_, ?_⟩
  · have x1 : (e • E₁ᵀ + s e • (E₂ᵀ * T)) * (e • E₁ + s e • (Q * E₂)) = (e * e) • (E₁ᵀ * E₁) +
        (s e * e) • (E₁ᵀ * (Q * E₂)) + (e * s e) • (E₂ᵀ * T * E₁) + (s e * s e) • (E₂ᵀ * T * (Q * E₂)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]; abel
    have x2 : E₂ᵀ * T * (Q * E₂) = 1 := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc T, hTQ, Matrix.one_mul, p22]
    rw [x1, he2, hs2, h2, h2', p11, x2, zero_smul, zero_smul, add_zero, add_zero, ← add_smul, h1, one_smul]
  · have mapE₁ : E₁ᵀ.map s = E₁ᵀ := by rw [Matrix.transpose_map, mapE]
    have e3 : (E₂ᵀ * T).map s = E₂ᵀ * G'ᵀ := by rw [Matrix.map_mul, mapT, Matrix.transpose_map, mapE]
    have hcm : (e • E₁ᵀ + s e • (E₂ᵀ * T)).map s = s e • E₁ᵀ + e • (E₂ᵀ * G'ᵀ) := Matrix.ext fun i j => by
      have a1 := congrFun (congrFun mapE₁ i) j; have a2 := congrFun (congrFun e3 i) j
      simp only [Matrix.map_apply] at a1 a2
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, ss,
        a1, a2]
    rw [hcm, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_transpose,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
    have x1 : (e • E₁ᵀ + s e • (E₂ᵀ * T)) * Γ * (s e • E₁ + e • (G' * E₂)) = (s e * e) • (E₁ᵀ * Γ * E₁) +
        (e * e) • (E₁ᵀ * Γ * (G' * E₂)) + (s e * s e) • (E₂ᵀ * T * Γ * E₁) + (e * s e) • (E₂ᵀ * T * Γ * (G' * E₂)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]; abel
    have x2 : E₁ᵀ * Γ * (G' * E₂) = 0 := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Γ, hΓG, Matrix.one_mul, p12]
    have x3 : E₂ᵀ * T * Γ * E₁ = 0 := by
      rw [Matrix.mul_assoc E₂ᵀ, hTΓ, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, p21, neg_zero]
    rw [x1, x2, x3, h2, h2', zero_smul, zero_smul, smul_zero, smul_zero, add_zero, add_zero, add_zero]

private theorem exists_isoW_split_pk {σ : E →ₐ[F] E} {B : Base F E} {W : Spc F E d} {r s : ℕ}
    (hB : GoodK σ B) (hW : W.IsSkew σ B r s) (hnd : 2 * n ≤ d) (t : E →ₐ[F] Fv F v) :
    ∃ Y R, IsIsoW σ W v (n := n) Y R := by
  have hc := hB.cm; have hσ := cm_conj_conj hc
  have hss : ∀ y : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (hσ x)
    | add _ _ hx hy => simp only [map_add (f := _), hx, hy]
  have extAt : ∀ {ι κ : Type} {M M' : Matrix ι κ (AE F E)}, At (evFin F v) M → At (evFin F v) M' →
      M.map (compFin F E v) = M'.map (compFin F E v) → M = M' := fun h h' e =>
    Matrix.ext fun i j => sub_eq_zero.1 (eq_zero_of_at (v := v)
      (fun u hu => congrFun (congrFun (at_sub h h' u hu) i) j)
      (by rw [map_sub, sub_eq_zero]; exact congrFun (congrFun e i) j))
  have atSg : ∀ {ι κ : Type} (M : Matrix ι κ (Fv F v ⊗[F] E)), At (evFin F v) (M.map (sgE E v)) :=
    fun _ u hu => Matrix.ext fun _ _ => at_sgE _ u hu
  have cmpSg : ∀ {ι κ : Type} (M : Matrix ι κ (Fv F v ⊗[F] E)), (M.map (sgE E v)).map (compFin F E v) = M :=
    fun _ => Matrix.ext fun _ _ => comp_sgE _
  obtain ⟨a, g, l, ha, hal, hΓ, G', hG', hi⟩ :=
    GlobalTheory.ThK.Dbl.Frame.exists_loc_k hB (Or.inr hW) (det_ne_zero hW) v
  let ι := inclR (F := F) (E := E) (Fv F v); let c' := sigR (Fv F v) σ
  have mJ : ((W.J.map ι).map c')ᵀ = -W.J.map ι := Matrix.ext fun i j => by
    change c' (ι (W.J j i)) = -ι (W.J i j)
    rw [show c' (ι (W.J j i)) = ι (σ (W.J j i)) from rfl, hW.skew i j, map_neg]
  have sk : ((g.1ᵀ * W.J.map ι * g.1.map c').map c')ᵀ = -(g.1ᵀ * W.J.map ι * g.1.map c') := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      show (g.1.map c').map c' = g.1 from Matrix.ext fun _ _ => hss _, mJ, Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have sI := sigR_splitIdem hc t
  obtain ⟨c, ρ, ic, iρ, hcρ, hgr⟩ := core_pk (intLoc F E v) c' (fun _ hx => sigR_mem_intLoc σ hx) hss
    (splitIdem_mem hc t) (by change _ + sigR _ σ _ = 1; rw [sI]; ring)
    (by change _ * sigR _ σ _ = 0; rw [sI, mul_sub, mul_one, splitIdem_mul_self hc t, sub_self]) hnd hΓ hG' hi sk
  let Y₀ := c * a.1ᵀ; let R₀ := (a⁻¹).1ᵀ * ρ
  refine ⟨Y₀.map (sgE E v), R₀.map (sgE E v), ⟨fun i => ?_, ?_, ?_, fun z hz j => ?_⟩⟩
  · refine (PositivityTheory.ThKG.Loc.Cone.Vf.mem_latW_loc W _).2 ⟨fun u hu => funext fun _ => at_sgE _ u hu, ?_⟩
    convert (ha (c i)).1 (ic i) using 1
    funext j; change compFin F E v (sgE E v (Y₀ i j)) = _
    rw [comp_sgE]; simp only [Y₀, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, mul_comm]
  · refine extAt (at_mul_left (atSg _) _) (at_eM_pk n) ?_
    have e1 : (eM v n : Matrix (Fin n) (Fin n) (AE F E)).map (compFin F E v) = 1 := Matrix.ext fun i j => by
      change compFin F E v (sg v 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) = _
      rw [← sgE_comp, comp_sgE, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.map_mul, cmpSg, cmpSg, e1, Matrix.mul_assoc, ← Matrix.mul_assoc a.1ᵀ, ← Matrix.transpose_mul,
      Units.inv_mul, Matrix.transpose_one, Matrix.one_mul, hcρ]
  · refine extAt (at_mul_left (at_mul_left (atSg _) _) _) at_zero ?_
    have e1 : (incM F W.J).map (compFin F E v) = W.J.map ι :=
      Matrix.ext fun i k => congrArg (· ⊗ₜ[F] W.J i k) (map_one (evFin F v))
    have e2 : (((Y₀.map (sgE E v)).map (cA σ))ᵀ).map (compFin F E v) = (Y₀.map c')ᵀ := Matrix.ext fun i j => by
      change compFin F E v (cA σ (sgE E v (Y₀ j i))) = c' (Y₀ j i)
      rw [GlobalTheory.ThK.Dbl.Vf2.comp_cA, comp_sgE]
    have e3 : a.1.map c' = c' l.1 • g.1.map c' := Matrix.ext fun i j => by
      change c' (a.1 i j) = c' l.1 * c' (g.1 i j); rw [hal, Matrix.smul_apply, smul_eq_mul, map_mul]
    rw [Matrix.map_mul, Matrix.map_mul, cmpSg, e1, e2]
    simp only [Y₀, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose]
    rw [e3, hal]
    have e4 : c * (l.1 • g.1)ᵀ * W.J.map ι * ((c' l.1 • g.1.map c') * (c.map c')ᵀ) =
        (l.1 * c' l.1) • (c * (g.1ᵀ * W.J.map ι * g.1.map c') * (c.map c')ᵀ) := by
      simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; rw [mul_comm]
    rw [e4, hgr, smul_zero, Matrix.map_zero _ (map_zero _)]
  · obtain ⟨z1, z2⟩ := (PositivityTheory.ThKG.Loc.Cone.Vf.mem_latW_loc W z).1 hz
    have eT : z ᵥ* R₀.map (sgE E v) = (R₀.map (sgE E v))ᵀ *ᵥ z := (Matrix.mulVec_transpose _ _).symm
    have hat : At (evFin F v) (z ᵥ* R₀.map (sgE E v)) := eT ▸ at_mulVec_right _ z1
    refine mem_Oh_pk (fun u hu => congrFun (hat u hu) j) ?_
    let y := (a⁻¹).1 *ᵥ (compFin F E v ∘ z)
    have iy := (ha y).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])
    have e1 : compFin F E v ((z ᵥ* R₀.map (sgE E v)) j) = (y ᵥ* ρ) j := by
      rw [eT, RingHom.map_mulVec, Matrix.transpose_map, cmpSg, Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose]
    rw [e1]; show ∑ k, y k * ρ k j ∈ intLoc F E v; exact sum_mem fun k _ => mul_mem (iy k) (iρ k j)

private theorem exists_isoW_inert_pk {σ : E →ₐ[F] E} {B : Base F E} {W : Spc F E d} {r s : ℕ}
    (hB : GoodK σ B) (hW : W.IsSkew σ B r s) (h2 : 2 * n ≤ d) {w : HeightOneSpectrum (𝓞 E)}
    (hw : IsInertAt F E v w) : ∃ Y R, IsIsoW σ W v (n := n) Y R := by
  have h : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw h
  obtain ⟨a, ha, _, -, hg⟩ := exists_frame hB.cm hw h hc hW
  let f : Fin n → Fin d := Fin.castLE (by omega)
  obtain ⟨Y, hY, eY⟩ := mat_surj h (a.1ᵀ.submatrix f id)
  obtain ⟨R, hR, eR⟩ := mat_surj h ((a⁻¹).1ᵀ.submatrix id f)
  refine ⟨Y, R, fun i => ?_, ?_, ?_, fun z hz j => ?_⟩
  · refine (mem_latW_iff hw h W _).2 ⟨fun u hu => congrFun (hY u hu) i, ?_⟩
    have e : piE h ∘ Y i = a.1 *ᵥ fun k => (1 : Matrix (Fin d) (Fin d) (w.adicCompletion E)) k (f i) :=
      funext fun k => by
      have e1 : piE h (Y i k) = a.1 k (f i) := congrFun (congrFun eY i) k
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, e1]
    rw [e]; exact (ha _).1 fun k => one_int k (f i)
  · refine mat_inj hw h (at_sub (at_mul_left hY _) (at_eM_pk n)) ?_
    have hpi : (eM v n).map (piE h) = 1 := Matrix.ext fun i j => by
      change piE h (sg v 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) = _
      rw [← sgE_comp]; change toCompl h (compFin F E v (sgE E v _)) = _
      rw [comp_sgE, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.map_mul, eY, eR, hpi]
    change (a.1ᵀ * (a⁻¹).1ᵀ).submatrix f f = _
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.submatrix_one _ (Fin.castLE_injective _)]
  · refine mat_inj hw h (at_sub (at_mul_left (at_mul_left hY _) _) at_zero) ?_
    have e := map_gram hc W.J Yᵀ Yᵀ
    rw [Matrix.transpose_transpose, show Yᵀ.map (piE h) = a.1.submatrix id f by rw [Matrix.transpose_map, eY]; rfl] at e
    refine e.trans (Matrix.ext fun i j => (congrFun (congrFun hg (f i)) (f j)).trans ?_)
    have := i.2; have := j.2
    rw [Matrix.smul_apply]; simp only [antiJ, f, Fin.val_castLE]; rw [ite_eq_right (by omega)]; simp
  · obtain ⟨_, h4⟩ := (mem_latW_iff hw h W z).1 hz
    rw [← Matrix.mulVec_transpose]
    refine mem_Oh_pk (fun u hu => congrFun (at_mulVec_left (at_transpose hR) z u hu) j) ((mem_intLoc_iff hw h _).2 ?_)
    have e := congrFun (piE_mulVec h Rᵀ z) j
    rw [Function.comp_apply] at e
    change piE h ((Rᵀ *ᵥ z) j) ∈ Ov E w
    rw [e, show Rᵀ.map (piE h) = (a⁻¹).1.submatrix f id by rw [Matrix.transpose_map, eR]; rfl]
    exact coord_int ha h4 (f j)

end UpperTheory.LatD

open UpperTheory.LatD in
theorem UpperTheory.exists_weilLatticeDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
      (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), GoodK σ B → X.IsHerm σ B r s →
      W.IsSkew σ B r' s' → 2 * n ≤ d → ∀ v : Pl F, ∃ Λ x₁ R ϖ, LatData σ X W v Λ x₁ R ϖ := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW hnd v
  have ⟨Y, R, hY⟩ : ∃ Y R, IsIsoW σ W v (n := n) Y R := by
    by_cases ht : Nonempty (E →ₐ[F] Fv F v)
    · obtain ⟨t⟩ := ht; exact exists_isoW_split_pk hB hW hnd t
    · obtain ⟨w, hw⟩ := inertof_proof_k F E σ B hB v (not_nonempty_iff.1 ht)
      exact exists_isoW_inert_pk hB hW hnd hw
  obtain ⟨b, c, hF⟩ := UpperTheory.unitaryLattice_exists_frame F E n X v hX.lat
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  let ϖ : Fv F v := ((π : F) : v.adicCompletion F)
  have heϖ : Valued.v ϖ = v.valuation F π := v.valuedAdicCompletion_eq_valuation' π
  have hϖ0 : ϖ ≠ 0 := fun h0 => by rw [h0, map_zero, hπ] at heϖ; exact absurd heϖ.symm (by simp)
  have hϖ1 : Valued.v ϖ < 1 := by rw [heϖ, hπ]; exact compareOfLessAndEq_eq_lt.mp rfl
  have hact : ∀ a ∈ abelian₂ (E := E) v b c, ∀ z ∈ latW X v, a *ᵥ z ∈ latW X v := fun a ha z hz => by
    have e : a *ᵥ z = b *ᵥ ((c * a * b) *ᵥ (c *ᵥ z)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; congr 1
      calc a = eM v n * a * eM v n := by rw [mul_eM_pk (at_mul_right _ ha.1), eM_mul_pk ha.1]
        _ = (b * c) * a * (b * c) := by rw [hF.bc]
        _ = b * (c * a * b) * c := by simp only [Matrix.mul_assoc]
    rw [e, show b *ᵥ ((c * a * b) *ᵥ (c *ᵥ z)) = ∑ j, fun i => ((c * a * b) *ᵥ (c *ᵥ z)) j * b i j from
      funext fun i => by simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]]
    exact sum_mem fun j _ => lat_smul_pk (show ∑ k, (c * a * b) j k * (c *ᵥ z) k ∈ Oh E v from
      sum_mem fun k _ => oh_mul_pk (ha.2 j k) (hF.coord z hz k)) (hF.col j)
  refine ⟨abelian₂ (E := E) v b c, b * Y, R * c, ϖ,
    { at_mem := fun _ ha => ha.1
      one_mem := ⟨at_eM_pk n, fun i j => by
        rw [mul_eM_pk hF.at_c, hF.cb]
        by_cases h : i = j
        · subst h; simpa [eM] using oh_sg_pk (E := E) (v := v) (one_mem _)
        · simp [eM, h, zero_mem]⟩
      mul_mem := fun a ha a' ha' => ⟨at_mul_left ha.1 a', fun i j => by
        have e : c * (a * a') * b = (c * a * b) * (c * a' * b) := by
          calc c * (a * a') * b = c * (a * eM v n * a') * b := by rw [mul_eM_pk ha.1]
            _ = c * (a * (b * c) * a') * b := by rw [hF.bc]
            _ = (c * a * b) * (c * a' * b) := by simp only [Matrix.mul_assoc]
        rw [e, Matrix.mul_apply]; exact sum_mem fun k _ => oh_mul_pk (ha.2 i k) (ha'.2 k j)⟩
      smul_mem := fun t ht a ha => ⟨fun u hu => by rw [smul_comm, ha.1 u hu, smul_zero], fun i j => by
        rw [Matrix.mul_smul, Matrix.smul_mul]; exact oh_smul_pk ht (ha.2 i j)⟩
      act := fun a ha γ hγ => gam_ind_pk (p := fun γ => a * γ ∈ latAtV X W v)
        (fun z hz y hy => by rw [Matrix.mul_vecMulVec]; exact vmv_mem_pk (hact a ha z hz) hy)
        (by simp [zero_mem]) (fun _ _ h h' => by rw [Matrix.mul_add]; exact add_mem h h')
        (fun _ h => by rw [Matrix.mul_neg]; exact neg_mem h) hγ
      x_mem := by
        rw [show b * Y = ∑ k, vecMulVec (fun i => b i k) (Y k) from
          Matrix.ext fun i j => by simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply]]
        exact sum_mem fun k _ => vmv_mem_pk (hF.col k) (hY.what₂ k)
      gram := by
        rw [show (b * Y).map (cA σ) = b.map (cA σ) * Y.map (cA σ) from Matrix.map_mul (f := (cA σ).toRingHom),
          Matrix.transpose_mul,
          show b * Y * incM F W.J * ((Y.map (cA σ))ᵀ * (b.map (cA σ))ᵀ) =
            b * (Y * incM F W.J * (Y.map (cA σ))ᵀ) * (b.map (cA σ))ᵀ by simp only [Matrix.mul_assoc],
          hY.gram, Matrix.mul_zero, Matrix.zero_mul]
      right := by
        rw [show b * Y * (R * c) = b * (Y * R) * c by simp only [Matrix.mul_assoc], hY.right, mul_eM_pk hF.at_b, hF.bc]
      r_mem := fun γ hγ => ⟨at_mul_right _ (at_mul_right _ hF.at_c),
        gam_ind_pk (p := fun γ => ∀ i j, (c * (γ * (R * c)) * b) i j ∈ Oh E v)
          (fun z hz y hy i j => by
            have e : c * (vecMulVec z y * (R * c)) * b = vecMulVec (c *ᵥ z) (sg v 1 • (y ᵥ* R)) := by
              rw [show c * (vecMulVec z y * (R * c)) * b = c * vecMulVec z y * R * (c * b) by
                simp only [Matrix.mul_assoc], hF.cb, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.mul_smul,
                Matrix.mul_one]
              ext i j; simp [vecMulVec_apply]
            rw [e, vecMulVec_apply]
            exact oh_mul_pk (hF.coord z hz i) (oh_smul_pk (one_mem _) (hY.coord y hy j)))
          (by simp [zero_mem])
          (fun _ _ h h' i j => by rw [Matrix.add_mul, Matrix.mul_add, Matrix.add_mul]; exact add_mem (h i j) (h' i j))
          (fun _ h i j => by rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem (h i j)) hγ⟩
      ϖ_ne := hϖ0
      ϖ_mem := hϖ1.le
      unit := UpperTheory.latticeOrder_exists_inverse_one_add_uniformizer_smul F E n X v b c hF ϖ hϖ1.le hϖ1
      small := (UpperTheory.mem_nhds_one_of_congruence_latticeOrder F E σ n X v b c hF ϖ hϖ0 hϖ1).1
      nbhd := (UpperTheory.mem_nhds_one_of_congruence_latticeOrder F E σ n X v b c hF ϖ hϖ0 hϖ1).2 }⟩

end
end

noncomputable section
namespace UpperTheory.TP.BA
open scoped Classical
open UpperTheory.TP UpperTheory.TP.BA
open GlobalTheory.LatVac (psiAt locCo liftV at_liftV evFin_liftV latAtV_at_stable)
open PositivityTheory.ThKH.Iwas (at_mul_right at_add at_sub mul_sg ev_sg)
open PositivityTheory.ThKH.Locrep (one_mem_UAt mul_mem_UAt)
private theorem sep_dual_pk {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ) (Λ L : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (hle : Λ ≤ L)
    (hdual : ∀ z, z ∈ Λ ↔ ∀ l ∈ Λ, ψ₀ (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1)
    (hst : ∀ a ∈ v.adicCompletionIntegers F, ∀ l ∈ L, a • l ∈ L)
    (c₀ : Fv F v) (hc₀ : c₀ ≠ 0)
    (hbd : ∀ l ∈ L, ∀ i, c₀ * l.1 i ∈ v.adicCompletionIntegers F ∧ c₀ * l.2 i ∈ v.adicCompletionIntegers F)
    (ha : ∀ x ∈ v.adicCompletionIntegers F, ψ₀ (1 * x) = 1)
    (y : (κ → Fv F v) × (κ → Fv F v)) (hy : y ∉ L) :
    ∃ u : (κ → Fv F v) × (κ → Fv F v), (∀ l ∈ L, ψ₀ (u.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ u.2) = 1) ∧
      ψ₀ (u.1 ⬝ᵥ y.2 - y.1 ⬝ᵥ u.2) ≠ 1 := by
  let O := v.adicCompletionIntegers F
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ψ₀ x₀ ≠ 1 := by_contra fun h => by
    push Not at h; exact hy (hle ((hdual y).2 fun _ _ => h _))
  have hx0 : x₀ ≠ 0 := by rintro rfl; exact hx₀ (AddChar.map_zero_eq_one ψ₀)
  let I : Ideal O :=
    { carrier := {o | ∀ y ∈ O, ψ₀ (x₀ * o * y) = 1}
      add_mem' := fun {p q} hp hq y hy => by
        rw [show x₀ * ((p + q : O) : Fv F v) * y = x₀ * p * y + x₀ * q * y by push_cast; ring,
          AddChar.map_add_eq_mul, hp y hy, hq y hy, one_mul]
      zero_mem' := fun _ _ => by simp
      smul_mem' := fun r p hp y hy => by
        rw [show x₀ * ((r • p : O) : Fv F v) * y = x₀ * p * (r * y) by simp only [smul_eq_mul]; push_cast; ring]
        exact hp _ (mul_mem r.2 hy) }
  have key : ∀ x, (∀ y ∈ O, ψ₀ (x * y) = 1) → x₀⁻¹ * x ∈ O := fun x hx => by
    by_cases hx' : x = 0
    · subst hx'; simp
    · refine (O.mem_or_inv_mem (x₀⁻¹ * x)).resolve_right fun h => hx₀ ?_
      have := hx _ h; rwa [show x * (x₀⁻¹ * x)⁻¹ = x₀ by field_simp] at this
  obtain ⟨b, hb⟩ := (IsPrincipalIdealRing.principal I).principal
  have hbI : b ∈ I := by rw [hb]; exact Submodule.mem_span_singleton_self b
  have hmem : ∀ o, o ∈ I ↔ ∃ t : O, o = t * b := fun o => by rw [hb, Submodule.mem_span_singleton]; simp [eq_comm]
  have hin : ∀ x hx, (⟨_, key x hx⟩ : O) ∈ I := fun x hx y hy => by
    simpa [hx0, mul_assoc, mul_inv_cancel_left₀] using hx y hy
  have hb0 : (b : Fv F v) ≠ 0 := fun h0 => by
    have h0' : b = 0 := by exact_mod_cast h0
    obtain ⟨t, ht⟩ := (hmem _).1 (hin 1 ha); rw [h0', mul_zero] at ht
    have := congrArg Subtype.val ht; simp [hx0] at this
  let c : Fv F v := x₀ * b
  have hc0 : c ≠ 0 := mul_ne_zero hx0 hb0
  have hc : ∀ x, (∀ y ∈ O, ψ₀ (x * y) = 1) ↔ c⁻¹ * x ∈ O := fun x =>
    ⟨fun hx => by
      obtain ⟨t, ht⟩ := (hmem _).1 (hin x hx)
      have h2 : x₀⁻¹ * x = t * b := by simpa using congrArg Subtype.val ht
      rw [show c⁻¹ * x = t by dsimp [c]; rw [mul_inv, mul_comm x₀⁻¹, mul_assoc, h2]; field_simp]; exact t.2,
     fun hx y hy => by
      have hh := hbI ((c⁻¹ * x) * y) (mul_mem hx hy)
      rwa [show x₀ * b * (c⁻¹ * x * y) = x * y by dsimp [c]; field_simp] at hh⟩
  let L' : Submodule O ((κ → Fv F v) × (κ → Fv F v)) :=
    { carrier := L, add_mem' := fun h h' => L.add_mem h h', zero_mem' := L.zero_mem,
      smul_mem' := fun t _ hl => hst (t : Fv F v) t.2 _ hl }
  let φ : ((κ → O) × (κ → O)) →ₗ[O] ((κ → Fv F v) × (κ → Fv F v)) :=
    { toFun := fun x => (fun i => c₀⁻¹ * (x.1 i : Fv F v), fun i => c₀⁻¹ * (x.2 i : Fv F v))
      map_add' := fun _ _ => by ext i <;> simp [mul_add]
      map_smul' := fun _ _ => by ext i <;> simp [Algebra.smul_def] <;> ring }
  have hle' : L' ≤ LinearMap.range φ := fun l hl =>
    ⟨(fun i => ⟨c₀ * l.1 i, (hbd l hl i).1⟩, fun i => ⟨c₀ * l.2 i, (hbd l hl i).2⟩), by ext i <;> simp [φ, hc₀]⟩
  have : IsNoetherian O (LinearMap.range φ) := isNoetherian_of_isNoetherianRing_of_finite _ _
  have : IsNoetherian O L' := isNoetherian_of_le hle'
  have hspan : Submodule.span (Fv F v) (L' : Set ((κ → Fv F v) × (κ → Fv F v))) = ⊤ := eq_top_iff.2 fun w _ => by
    obtain ⟨t, ht0, ht⟩ := GlobalTheory.LatBound.exists_mul_mem_integers v
      (fun s : κ ⊕ κ => Sum.elim (fun k => (c * c₀)⁻¹ * w.1 k) (fun k => (c * c₀)⁻¹ * w.2 k) s)
    have hw : t • w ∈ L := hle ((hdual _).2 fun l hl => by
      have hm : c⁻¹ * ((t • w).1 ⬝ᵥ l.2 - l.1 ⬝ᵥ (t • w).2) ∈ O := by
        rw [mul_sub]; simp only [dotProduct, Finset.mul_sum]
        refine sub_mem (sum_mem fun k _ => ?_) (sum_mem fun k _ => ?_)
        · convert mul_mem (ht (Sum.inl k)) (hbd l (hle hl) k).2 using 1
          simp only [Sum.elim_inl, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]; field_simp
        · convert mul_mem (ht (Sum.inr k)) (hbd l (hle hl) k).1 using 1
          simp only [Sum.elim_inr, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; field_simp
      have h1 := (hc _).2 hm 1 (one_mem _); rwa [mul_one] at h1)
    rw [show w = t⁻¹ • (t • w) by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hw)
  have : L'.IsLattice (Fv F v) := Submodule.IsLattice.of_fg (Fv F v) (Module.Finite.iff_fg.1 inferInstance)
  have : L'.IsFullLattice (Fv F v) := ⟨hspan⟩
  let ψ' : AddChar (Fv F v) ℂ := ψ₀.compAddMonoidHom (AddMonoidHom.mulLeft c)
  have hsep : ∀ x, (∀ y : O, ψ' (x * algebraMap O (Fv F v) y) = 1) ↔ x ∈ (algebraMap O (Fv F v)).range := fun x => by
    have h := hc (c * x); rw [show c⁻¹ * (c * x) = x by field_simp] at h
    exact ⟨fun hx => ⟨⟨x, h.1 fun y hy => by simpa [ψ', mul_assoc] using hx ⟨y, hy⟩⟩, rfl⟩,
      by rintro ⟨o, rfl⟩ y; simpa [ψ', mul_assoc] using h.2 o.2 y y.2⟩
  obtain ⟨l, h1, h2⟩ := GlobalTheory.ThK.Dbl.Bmp.sep ψ' hsep L' hy
  let e : κ → κ → Fv F v := fun k j => if k = j then 1 else 0
  let A : (κ → Fv F v) →ₗ[Fv F v] Fv F v := l ∘ₗ LinearMap.inl _ _ _
  let Bm : (κ → Fv F v) →ₗ[Fv F v] Fv F v := l ∘ₗ LinearMap.inr _ _ _
  have hl : ∀ z, l z = ∑ k, z.1 k * A (e k) + ∑ k, z.2 k * Bm (e k) := fun z => by
    have h1' := LinearMap.pi_apply_eq_sum_univ A z.1; have h2' := LinearMap.pi_apply_eq_sum_univ Bm z.2
    simp only [smul_eq_mul] at h1' h2'; rw [← h1', ← h2']
    conv_lhs => rw [show z = (z.1, 0) + (0, z.2) by simp, map_add (f := _)]
    rfl
  have hu : ∀ z, ψ₀ ((fun k => c * Bm (e k)) ⬝ᵥ z.2 - z.1 ⬝ᵥ (fun k => -(c * A (e k)))) = ψ' (l z) := fun z => by
    change _ = ψ₀ (c * l z); rw [hl, mul_add, Finset.mul_sum, Finset.mul_sum]; congr 1
    simp only [dotProduct]; rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, add_comm]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring
  exact ⟨(fun k => c * Bm (e k), fun k => -(c * A (e k))), fun z hz => (hu z).trans (h1 z hz),
    fun h => h2 ((hu y).symm.trans h)⟩

private theorem schr_comp_pk {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ]
    (ψ : AddChar R ℂ) (w w' : (κ → R) × (κ → R)) (f : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' f) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') f := funext fun x => by
  simp only [schr, Prod.fst_add, Prod.snd_add, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc, ← map_add_eq_mul, ← map_add_eq_mul, add_assoc x]; congr 2
  simp only [add_dotProduct, dotProduct_add]; linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_mul_self (2 : R)

private theorem cong_key_pk {A : Type} [Ring A] {e s m m' α β q q' : A} (hs : ∀ a : A, s * a = a * s)
    (h : m * (e - s * β) = e + s * α) (hmm : m' * m = 1) (hq : (e - s * β) * q = e) (hq' : (e + s * α) * q' = e)
    (eq : e * q = q) (eq' : e * q' = q') (eα : α * e = α) (eβ : β * e = β) (hm : (m - 1) * e = m - 1)
    (hm' : (m' - 1) * e = m' - 1) :
    m - 1 = s * (α + β * q + s * (α * (β * q))) ∧ m' - 1 = s * (-β - α * q' + s * (β * (α * q'))) := by
  have a1 : q = e + s * (β * q) := by
    have : e * q - s * β * q = e := by rw [← sub_mul]; exact hq
    rw [eq] at this; rw [← this, mul_assoc]; abel
  have a2 : q' = e - s * (α * q') := by
    have : e * q' + s * α * q' = e := by rw [← add_mul]; exact hq'
    rw [eq'] at this; rw [← this, mul_assoc]; abel
  have b1 : m * e = (e + s * α) * q := by rw [← h, mul_assoc, hq]
  have b2 : m' * e = (e - s * β) * q' := by
    calc m' * e = m' * ((e + s * α) * q') := by rw [hq']
      _ = m' * (m * (e - s * β) * q') := by rw [h]
      _ = (m' * m) * (e - s * β) * q' := by simp only [mul_assoc]
      _ = _ := by rw [hmm, one_mul]
  have c : ∀ a b : A, a * (s * b) = s * (a * b) := fun a b => by rw [← mul_assoc, ← hs a, mul_assoc]
  have a3 : α * q = α + s * (α * (β * q)) := by conv_lhs => rw [a1]; rw [mul_add, eα, c]
  have a4 : β * q' = β - s * (β * (α * q')) := by conv_lhs => rw [a2]; rw [mul_sub, eβ, c]
  exact ⟨by rw [← hm, sub_mul, one_mul, b1]
            calc (e + s * α) * q - e = q + s * (α * q) - e := by rw [add_mul, eq, mul_assoc]
              _ = (e + s * (β * q)) + s * (α + s * (α * (β * q))) - e := by rw [a3, ← a1]
              _ = _ := by rw [mul_add, mul_add, mul_add]; abel,
         by rw [← hm', sub_mul, one_mul, b2]
            calc (e - s * β) * q' - e = q' - s * (β * q') - e := by rw [sub_mul, eq', mul_assoc]
              _ = (e - s * (α * q')) - s * (β - s * (β * (α * q'))) - e := by rw [a4, ← a2]
              _ = _ := by simp only [mul_add, mul_sub, mul_neg]; abel⟩

private theorem at_mat_inv_pk {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} {σ : E →ₐ[F] E} {X : Spc F E n} {v : Pl F} {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) :
    g⁻¹ ∈ UAt σ X (evFin F v) := by
  have e : mat g⁻¹ - 1 = -mat g⁻¹ * (mat g - 1) := by
    rw [mul_sub, neg_mul, show mat g⁻¹ * mat g = 1 from g.1.inv_mul]; simp [neg_add_eq_sub]
  show At (evFin F v) (mat g⁻¹ - 1); rw [e]; exact at_mul_right _ hg

private theorem mem_UAt_of_locGrp_pk {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} {σ : E →ₐ[F] E} {X : Spc F E n} {v : Pl F} {g : UA σ X.J}
    (hg : g ∈ locGrp σ X v) : g ∈ UAt σ X (evFin F v) := by
  induction hg using Subgroup.closure_induction with
  | mem _ hx => exact hx
  | one => exact one_mem_UAt X v
  | mul _ _ _ _ hx hy => exact mul_mem_UAt hx hy
  | inv _ _ hx => exact at_mat_inv_pk hx

theorem _root_.UpperTheory.TP.bumpAny_k : Tools_k → BumpAny_k := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hP hn hd v N hN
  obtain ⟨ω, ρ, L⟩ := PositivityTheory.ThKH.Locrep.locRepEx_k F E σ n d B X W M om
    ⟨hP.base, ⟨n, 0, hP.herm⟩, ⟨d, 0, hP.skew⟩, hP.good, χX, χW, hP.weil⟩ v
  obtain ⟨Λ, x₁, r, ϖ, D⟩ := UpperTheory.exists_weilLatticeDatum F E σ B n d X W n 0 d 0 hP.base hP.herm hP.skew hd v
  obtain ⟨hvS, hv0, θ, hθ, hvac⟩ := hP.good.vac v
  have hat : ∀ γ ∈ latAtV X W v, At (evFin F v) γ := (latAtV_at_stable X W v).1
  have hOlat := (latAtV_at_stable X W v).2
  have hone : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := one_mem_UAt W v
  obtain ⟨U, hU, hUf⟩ := (T.acts F E σ B n d X W M χX χW om n 0 d 0 hP v).2.2 (M.vac v) hvS
  have hU1 : {g : UA σ X.J | (g, (1 : UA σ W.J)) ∈ U} ∈ 𝓝 (1 : UA σ X.J) :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (show U ∈ 𝓝 ((1 : UA σ X.J), 1) from hU)
  have hI : {g : UA σ X.J | GlobalTheory.ThK.Dbl.IntAt v g} ∈ 𝓝 (1 : UA σ X.J) :=
    (GlobalTheory.ThK.Dbl.Euler.isOpen_int (σ := σ) hP.herm.lat v).mem_nhds (one_mem _)
  obtain ⟨k₀, hk₀⟩ := D.small _ (Filter.inter_mem hN (Filter.inter_mem hU1 hI))
  let k := k₀ + 1
  have hϖO : ∀ m : ℕ, ϖ ^ m ∈ v.adicCompletionIntegers F := fun m => pow_mem D.ϖ_mem m
  let s := sg v (ϖ ^ k); let s' := sg v (ϖ ^ k)⁻¹
  have sg_mul : ∀ a b : Fv F v, sg v a * sg v b = sg v (a * b) := fun _ _ => by rw [mul_sg, ev_sg]
  have sg_one : ∀ {N : Type} [AddCommGroup N] [Module (AF F) N] {x : N}, At (evFin F v) x → sg v 1 • x = x :=
    fun hx => by
      have := hx (1 - sg v 1) (by rw [map_sub, map_one, ev_sg, sub_self])
      rwa [sub_smul, one_smul, sub_eq_zero, eq_comm] at this
  have ss : s * s' = sg v 1 := by rw [sg_mul, mul_inv_cancel₀ (pow_ne_zero _ D.ϖ_ne)]
  have hsΛ : ∀ a ∈ Λ, s • a ∈ Λ := fun a ha => D.smul_mem _ (hϖO k) a ha
  let H : Subgroup (UA σ X.J) :=
    { carrier := {g | g ∈ UAt σ X (evFin F v) ∧ (∃ a ∈ Λ, mat g - 1 = s • a) ∧ ∃ a ∈ Λ, mat g⁻¹ - 1 = s • a}
      one_mem' := ⟨one_mem_UAt X v, ⟨0, zero_mem _, by simp [mat]⟩, ⟨0, zero_mem _, by simp [mat]⟩⟩
      mul_mem' := fun ⟨a1, ⟨a, ha, ea⟩, ⟨a', ha', ea'⟩⟩ ⟨b1, ⟨b, hb, eb⟩, ⟨b', hb', eb'⟩⟩ => by
        have key : ∀ (p q a b : Matrix (Fin n) (Fin n) (AE F E)), p - 1 = s • a → q - 1 = s • b →
            p * q - 1 = s • (a + b + s • (a * b)) := fun p q a b e1 e2 => by
          rw [show p = 1 + s • a by rw [← e1]; abel, show q = 1 + s • b by rw [← e2]; abel]
          simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_add]; abel
        refine ⟨mul_mem_UAt a1 b1, ⟨_, add_mem (add_mem ha hb) (hsΛ _ (D.mul_mem _ ha _ hb)), key _ _ _ _ ea eb⟩,
          ⟨_, add_mem (add_mem hb' ha') (hsΛ _ (D.mul_mem _ hb' _ ha')), by
            rw [mul_inv_rev]; exact key _ _ _ _ eb' ea'⟩⟩
      inv_mem' := fun ⟨a1, p, q⟩ => ⟨at_mat_inv_pk a1, q, by rw [inv_inv]; exact p⟩ }
  have hsm : ∀ g ∈ H, g ∈ N ∩ ({g : UA σ X.J | (g, (1 : UA σ W.J)) ∈ U} ∩
      {g : UA σ X.J | GlobalTheory.ThK.Dbl.IntAt v g}) := fun g ⟨h1, h2, h3⟩ => hk₀ k (by omega) g h1 h2 h3
  have hx₁ := hat _ D.x_mem
  let x0 := s' • x₁
  have hx0 : At (evFin F v) x0 := fun u hu => by rw [smul_smul, mul_sg, hu, zero_mul, map_zero, zero_smul]
  have hsx0 : s • x0 = x₁ := by rw [smul_smul, ss, sg_one hx₁]
  let Sc (u : Matrix (Fin n) (Fin d) (AE F E)) (f : (Fin n × Fin d → Fv F v) → ℂ) :=
    schr (psiAt B.ψ v) (locCo M.co v u) f
  let Bf (u y : Matrix (Fin n) (Fin d) (AE F E)) : AF F := symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u y
  let φ := Sc x0 (M.vac v)
  let Q : Matrix (Fin n) (Fin d) (AE F E) → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ)
  have hSρ : ∀ u, At (evFin F v) u → ∀ f ∈ SB (Fin n × Fin d → Fv F v), Sc u f = ρ u f := fun u hu f hf =>
    (L.actsH u hu f hf _).1 (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu f)
  have hφS : φ ∈ SB (Fin n × Fin d → Fv F v) := by
    rw [show φ = ρ x0 (M.vac v) from hSρ _ hx0 _ hvS]; exact L.presH _ hx0 _ hvS
  have hφ0 : φ ≠ 0 := fun h0 => hv0 (by
    have hs0 : Sc (-x0) φ = M.vac v := by
      dsimp [φ, Sc]; rw [map_neg, schr_comp_pk, show (-locCo M.co v x0).1 ⬝ᵥ (locCo M.co v x0).2 -
        (locCo M.co v x0).1 ⬝ᵥ (-locCo M.co v x0).2 = 0 by simp [Prod.fst_neg, Prod.snd_neg, neg_dotProduct,
        dotProduct_neg],
        mul_zero, AddChar.map_zero_eq_one, one_smul, neg_add_cancel]; funext x; simp [schr]
    rw [h0] at hs0; rw [← hs0]; funext x; simp [Sc, schr])
  have hSv : ∀ γ ∈ latAtV X W v, Sc γ (M.vac v) = Q γ • M.vac v := fun γ hγ =>
    GlobalTheory.TensUniq.eq_of_tens_eq v (M.vac v) _ _ hvS fun r' hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ (hat γ hγ) (M.vac v) r' hr).symm.trans (hvac γ hγ r' hr)
  have hA : ∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) φ ((B.ψ (Bf γ x0) * Q γ) • φ) := fun γ hγ => by
    have hcm : Sc γ φ = (B.ψ (Bf γ x0) * Q γ) • φ := by
      have hcomm : Sc γ (Sc x0 (M.vac v)) = B.ψ (Bf γ x0) • Sc x0 (Sc γ (M.vac v)) := by
        dsimp [Sc, Bf]
        rw [schr_comp_pk, schr_comp_pk, add_comm (locCo M.co v x0), smul_smul,
          GlobalTheory.LatVac.DualLoc.psi_form M.co v B.ψ (hat γ hγ) x0, ← AddChar.map_add_eq_mul]
        congr 2
        linear_combination ((locCo M.co v γ).1 ⬝ᵥ (locCo M.co v x0).2 - (locCo M.co v x0).1 ⬝ᵥ (locCo M.co v γ).2) *
          invOf_mul_self (2 : Fv F v)
      rw [show φ = Sc x0 (M.vac v) from rfl, hcomm, hSv γ hγ]
      have hsmul : ∀ (c : ℂ) f, Sc x0 (c • f) = c • Sc x0 f := fun _ _ => funext fun _ => by
        simp only [Sc, schr, Pi.smul_apply, smul_eq_mul]; ring
      rw [hsmul, smul_smul]
    rw [← hcm]; exact GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ (hat γ hγ) φ
  have hsymp0 : ∀ (ξ : AE F E) (p q : Matrix (Fin n) (Fin n) (AE F E)),
      symp (R := AF F) (cA σ) ξ (incM F X.J) (incM F W.J) (p * x₁) (q * x₁) = 0 := fun ξ p q => by
    have h' : x₁.map (cA σ) * (incM F W.J)ᵀ * x₁ᵀ = 0 := by
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose D.gram
    have hm : (q * x₁).map (cA σ) = q.map (cA σ) * x₁.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)
    rw [symp, PositivityTheory.KCo.hTens_eq, hm, Matrix.transpose_mul]
    have ht : (x₁ᵀ * pᵀ * incM F X.J * (q.map (cA σ) * x₁.map (cA σ)) * (incM F W.J)ᵀ).trace = 0 := by
      calc _ = (x₁ᵀ * (pᵀ * incM F X.J * q.map (cA σ) * (x₁.map (cA σ) * (incM F W.J)ᵀ))).trace := by
             simp only [Matrix.mul_assoc]
        _ = ((pᵀ * incM F X.J * q.map (cA σ) * (x₁.map (cA σ) * (incM F W.J)ᵀ)) * x₁ᵀ).trace :=
          Matrix.trace_mul_comm _ _
        _ = 0 := by rw [Matrix.mul_assoc, h', Matrix.mul_zero, Matrix.trace_zero]
    rw [ht, mul_zero, map_zero]
  have hfix : ∀ g ∈ H, Acts (evFin F v) (om (g, 1)) φ φ := fun g hg => by
    obtain ⟨h1, ⟨a, ha, ea⟩, -⟩ := id hg
    have w1 : M.vac v = ω (g, 1) (M.vac v) := (L.acts g h1 1 hone _ hvS _).1 (hUf (g, 1) (hsm g hg).2.1 h1 hone)
    refine (L.acts g h1 1 hone φ hφS φ).2 ?_
    have hγ := D.act a ha x₁ D.x_mem
    have e1 : mat g * x0 * (mat (1 : UA σ W.J))ᵀ = x0 + a * x₁ := by
      rw [show mat (1 : UA σ W.J) = 1 from rfl, Matrix.transpose_one, Matrix.mul_one,
        show mat g = 1 + (mat g - 1) by abel, Matrix.add_mul, Matrix.one_mul, ea]
      congr 1; rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ss, sg_one (hat _ hγ)]
    have hb0 : Bf x0 (a * x₁) = 0 := by
      have := hsymp0 (-1) (s' • 1) a; rwa [Matrix.smul_mul, Matrix.one_mul] at this
    have hq1 : Q (a * x₁) = 1 := by
      show B.ψ _ = 1; rw [hsymp0 _ a a, mul_zero, AddChar.map_zero_eq_one]
    have hadd : Sc (x0 + a * x₁) (M.vac v) = Sc x0 (Sc (a * x₁) (M.vac v)) := by
      have hv := GlobalTheory.LatVac.DualLoc.evFin_form M.co v x0 (a * x₁)
      rw [show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x0 (a * x₁) = 0 from hb0, map_zero] at hv
      dsimp [Sc]; rw [map_add (f := _), schr_comp_pk, ← hv, mul_zero, AddChar.map_zero_eq_one, one_smul]
    have e2 := L.impl g h1 1 hone x0 hx0 (M.vac v) hvS
    rw [e1, ← w1, ← hSρ _ hx0 _ hvS, ← hSρ _ (at_add hx0 (hat _ hγ)) _ hvS, hadd, hSv _ hγ, hq1, one_smul] at e2
    exact e2.symm
  have hsep : ∀ g ∈ GlobalTheory.ThK.Dbl.locGrp σ X v, g ∉ H → ∃ (u : Matrix (Fin n) (Fin d) (AE F E)) (c c' : ℂ),
      At (evFin F v) u ∧ c ≠ c' ∧
        Acts (evFin F v) (M.co.rho B.ψ u) φ (c • φ) ∧ Acts (evFin F v) (M.co.rho B.ψ (mat g * u)) φ (c' • φ) :=
      fun g hgl hgH => by
    have hg := mem_UAt_of_locGrp_pk hgl; have hg' := at_mat_inv_pk hg
    have hgm : mat g * mat g⁻¹ = 1 := g.1.mul_inv
    let y := mat g⁻¹ * x0 - x0
    have hy : At (evFin F v) y := at_sub (at_mul_right _ hx0) hx0
    by_cases hc : ∀ a ∈ latAtV X W v, ∀ b ∈ latAtV X W v, y ≠ a + mat g⁻¹ * b
    · have hself := GlobalTheory.LatSelfDualAll.latAtV_selfDual_k F E σ B n d X W n 0 d 0 hP.base hP.herm hP.skew v
      have hsd := GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ (latAtV X W v) hat hself
      let Ssub : AddSubgroup (Matrix (Fin n) (Fin d) (AE F E)) :=
        { carrier := {z | ∃ a ∈ latAtV X W v, ∃ b ∈ latAtV X W v, z = a + mat g⁻¹ * b}
          add_mem' := by rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
                         exact ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', by rw [Matrix.mul_add]; abel⟩
          zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
          neg_mem' := by rintro _ ⟨a, ha, b, hb, rfl⟩; exact ⟨-a, neg_mem ha, -b, neg_mem hb, by
            rw [Matrix.mul_neg]; abel⟩ }
      have hmulat : ∀ (A : Matrix (Fin n) (Fin n) (AE F E)) (z : Matrix (Fin n) (Fin d) (AE F E)),
          At (evFin F v) z → At (evFin F v) (A * z) :=
        fun _ _ hz u hu => by rw [← Matrix.mul_smul, hz u hu, Matrix.mul_zero]
      have hloc_sm : ∀ (a : AF F) w, locCo M.co v (a • w) = evFin F v a • locCo M.co v w := fun _ _ => by
        simp only [locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]; ext k <;> simp [smul_eq_mul, map_mul]
      obtain ⟨c₁, hc₁0, hc₁⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hP.herm.lat.toIsLattice
        hP.skew.lat.toIsLattice
      obtain ⟨Mt, _, gm, hgm'⟩ := Tw.LatParam.latAtV_param X W hP.herm.lat.toIsLattice hP.skew.lat.toIsLattice
        v
      obtain ⟨c₂, hc₂0, hc₂⟩ := GlobalTheory.LatBound.exists_mul_mem_integers v
        (fun t : Bool × Mt × (Fin n × Fin d) =>
          if t.1 then (locCo M.co v (mat g⁻¹ * incM F (gm t.2.1))).1 t.2.2
          else (locCo M.co v (mat g⁻¹ * incM F (gm t.2.1))).2 t.2.2)
      have hb2 : ∀ b ∈ latAtV X W v, ∀ i, c₂ * (locCo M.co v (mat g⁻¹ * b)).1 i ∈ v.adicCompletionIntegers F ∧
          c₂ * (locCo M.co v (mat g⁻¹ * b)).2 i ∈ v.adicCompletionIntegers F := fun b hb i => by
        obtain ⟨a, rfl⟩ := (hgm' b).1 hb
        simp only [Matrix.mul_sum, Matrix.mul_smul, map_sum, hloc_sm, GlobalTheory.EmbChart.evFin_atPlace,
          Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          Finset.mul_sum]
        exact ⟨sum_mem fun m _ => by rw [mul_left_comm]; exact mul_mem (a m).2 (by simpa using hc₂ (true, m, i)),
          sum_mem fun m _ => by rw [mul_left_comm]; exact mul_mem (a m).2 (by simpa using hc₂ (false, m, i))⟩
      obtain ⟨c₀, hc₀, hb₁, hb₂⟩ : ∃ c : Fv F v, c ≠ 0 ∧
          (∀ x, c₁ * x ∈ v.adicCompletionIntegers F → c * x ∈ v.adicCompletionIntegers F) ∧
          ∀ x, c₂ * x ∈ v.adicCompletionIntegers F → c * x ∈ v.adicCompletionIntegers F := by
        rcases (v.adicCompletionIntegers F).mem_or_inv_mem (c₁⁻¹ * c₂) with h | h
        · exact ⟨c₂, hc₂0, fun x hx => by
            have := mul_mem h hx; rwa [show c₁⁻¹ * c₂ * (c₁ * x) = c₂ * x by field_simp] at this,
            fun _ hx => hx⟩
        · exact ⟨c₁, hc₁0, fun _ hx => hx, fun x hx => by
            have := mul_mem h hx; rwa [show (c₁⁻¹ * c₂)⁻¹ * (c₂ * x) = c₁ * x by field_simp] at this⟩
      have hbd : ∀ l ∈ Ssub.map (locCo M.co v), ∀ i, c₀ * l.1 i ∈ v.adicCompletionIntegers F ∧
          c₀ * l.2 i ∈ v.adicCompletionIntegers F := by
        rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩ i
        rw [map_add (f := _)]; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add]
        exact ⟨add_mem (hb₁ _ (hc₁ a ha i).1) (hb₂ _ (hb2 b hb i).1), add_mem (hb₁ _ (hc₁ a ha i).2) (hb₂ _ (hb2 b hb
          i).2)⟩
      have hst : ∀ t ∈ v.adicCompletionIntegers F, ∀ l ∈ Ssub.map (locCo M.co v), t • l ∈ Ssub.map (locCo M.co v) := by
        rintro t ht _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
        exact ⟨liftV v t • (a + mat g⁻¹ * b), ⟨liftV v t • a, hOlat t ht a ha, liftV v t • b, hOlat t ht b hb,
          by rw [smul_add, Matrix.mul_smul]⟩, by rw [hloc_sm, evFin_liftV]⟩
      have hle : (latAtV X W v).map (locCo M.co v) ≤ Ssub.map (locCo M.co v) := by
        rintro _ ⟨γ, hγ, rfl⟩; exact ⟨γ, ⟨γ, hγ, 0, zero_mem _, by simp⟩, rfl⟩
      have hyL : locCo M.co v y ∉ Ssub.map (locCo M.co v) := by
        rintro ⟨z, hzS, hz⟩; obtain ⟨a, ha, b, hb, rfl⟩ := id hzS
        have hSat : At (evFin F v) (a + mat g⁻¹ * b) := fun u hu => by
          rw [smul_add, hat a ha u hu, hmulat _ b (hat b hb) u hu, add_zero]
        have hzat : At (evFin F v) (a + mat g⁻¹ * b - y) := at_sub hSat hy
        have hz1 : liftV v 1 • (a + mat g⁻¹ * b - y) = a + mat g⁻¹ * b - y := by
          have := hzat (1 - liftV v 1) (by rw [map_sub, map_one, evFin_liftV, sub_self])
          rwa [sub_smul, one_smul, sub_eq_zero, eq_comm] at this
        have h0 : locCo M.co v (a + mat g⁻¹ * b - y) = 0 := by rw [map_sub, hz, sub_self]
        have he0 : M.co.e (a + mat g⁻¹ * b - y) = 0 := by
          rw [← hz1, map_smul]
          refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
          · simpa [smul_eq_mul, mul_comm] using at_liftV v 1 _ (congrFun (congrArg Prod.fst h0) k)
          · simpa [smul_eq_mul, mul_comm] using at_liftV v 1 _ (congrFun (congrArg Prod.snd h0) k)
        exact hc a ha b hb (sub_eq_zero.1 ((map_eq_zero_iff M.co.e M.co.e.injective).1 he0)).symm
      have hpt : ∀ x ∈ v.adicCompletionIntegers F, psiAt B.ψ v (1 * x) = 1 := fun x hx => by
        have h1 : (1 : Af F) ∈ GlobalTheory.Idele.adelicIdeal (GlobalTheory.StdDual.codiff F) := by
          simpa using (GlobalTheory.Idele.algebraMap_mem_adelicIdeal GlobalTheory.StdDual.codiff_ne_zero (1 : F)).2
            ((GlobalTheory.StdDual.one_le_codiff (F := F)) (FractionalIdeal.one_mem_one _))
        have h2 := (GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hP.base.std.1
          (GlobalTheory.LatVacArith.psi_fin_rat hP.base.std) 1).1 h1 (singleFin v x) fun w => by
            by_cases hw : w = v
            · subst hw; have e : (singleFin w x) w = x := evalV_singleFin_self w x; rwa [e]
            · have e : (singleFin v x) w = 0 := evalV_singleFin_ne hw x; rw [e]; exact zero_mem _
        rw [mul_one] at h2; rw [one_mul]; exact h2
      obtain ⟨w, hw1, hw2⟩ := sep_dual_pk v (psiAt B.ψ v) _ _ hle hsd hst c₀ hc₀ hbd hpt _ hyL
      let p : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) := (fun k => liftV v (w.1 k), fun k => liftV v (w.2 k))
      let u := M.co.e.symm p
      have huat : At (evFin F v) u := fun t ht => by
        rw [← map_smul, show t • p = 0 from Prod.ext (funext fun k => at_liftV v (w.1 k) t ht)
          (funext fun k => at_liftV v (w.2 k) t ht), map_zero]
      have hlu : locCo M.co v u = w := Prod.ext
        (funext fun k => by
          show evFin F v ((M.co.e (M.co.e.symm p)).1 k) = w.1 k; rw [LinearEquiv.apply_symm_apply];
          exact evFin_liftV v _)
        (funext fun k => by
          show evFin F v ((M.co.e (M.co.e.symm p)).2 k) = w.2 k; rw [LinearEquiv.apply_symm_apply];
          exact evFin_liftV v _)
      have hform := fun γ => GlobalTheory.LatVac.DualLoc.psi_form M.co v B.ψ huat γ
      have hu : u ∈ latAtV X W v := (hself u huat).2 fun γ hγ => by rw [hform, hlu]; exact hw1 _ (hle ⟨γ, hγ, rfl⟩)
      have hgu : mat g * u ∈ latAtV X W v := (hself _ (hmulat _ u huat)).2 fun γ hγ => by
        have e := GlobalTheory.SympInv.symp_act F E σ n d X W g 1 u (mat g⁻¹ * γ)
        rw [show mat (1 : UA σ W.J) = 1 from rfl, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_one,
          ← Matrix.mul_assoc, hgm, Matrix.one_mul] at e
        rw [e, hform, hlu]; exact hw1 _ ⟨mat g⁻¹ * γ, ⟨0, zero_mem _, γ, hγ, by simp⟩, rfl⟩
      have hne : B.ψ (Bf u y) ≠ 1 := by rw [hform, hlu]; exact hw2
      have hsympg : ∀ (ξ : AE F E) (u' y' : Matrix (Fin n) (Fin d) (AE F E)),
          symp (R := AF F) (cA σ) ξ (incM F X.J) (incM F W.J) (mat g * u') (mat g * y') =
            symp (R := AF F) (cA σ) ξ (incM F X.J) (incM F W.J) u' y' := fun ξ u' y' => by
        simpa [actAB, mat] using PositivityTheory.KCo.symp_act (R := AF F) (cA σ) ξ (incM F X.J) (incM F W.J) (g,
          (1 : UA σ W.J)) u' y'
      have hq : Q (mat g * u) = Q u := by show B.ψ _ = B.ψ _; rw [hsympg]
      have hb : Bf (mat g * u) x0 = Bf u (mat g⁻¹ * x0) := by
        have := hsympg (-1) u (mat g⁻¹ * x0); rwa [← Matrix.mul_assoc, hgm, Matrix.one_mul] at this
      refine ⟨u, _, _, hat u hu, fun h => hne ?_, hA u hu, hA _ hgu⟩
      have h3 : B.ψ (Bf u x0) = B.ψ (Bf (mat g * u) x0) :=
        mul_right_cancel₀ (show Q u ≠ 0 from (B.ψ.val_isUnit _).ne_zero) (by rw [h, hq])
      have hsub : Bf u y = Bf u (mat g⁻¹ * x0) - Bf u x0 := by
        simp only [Bf, y, M.co.form, map_sub, Prod.fst_sub, Prod.snd_sub, dotProduct_sub, sub_dotProduct]; ring
      rw [hsub, AddChar.map_sub_eq_div, ← hb, ← h3, div_self (B.ψ.val_isUnit _).ne_zero]
    · exfalso; apply hgH; push Not at hc; obtain ⟨a, ha, b, hb, e⟩ := hc
      have hα := D.r_mem a ha; have hβ := D.r_mem b hb
      let S : Matrix (Fin n) (Fin n) (AE F E) := s • 1
      have hSx : ∀ {l : ℕ} (x : Matrix (Fin n) (Fin l) (AE F E)), S * x = s • x := fun _ => by
        rw [Matrix.smul_mul, Matrix.one_mul]
      have hcomm : ∀ x : Matrix (Fin n) (Fin n) (AE F E), S * x = x * S := fun _ => by
        rw [hSx, Matrix.mul_smul, Matrix.mul_one]
      have e0 : mat g⁻¹ * (x₁ - s • b) = x₁ + s • a := by
        have e' : mat g⁻¹ * x0 = x0 + a + mat g⁻¹ * b := by rw [add_assoc, ← e]; dsimp [y]; abel
        calc mat g⁻¹ * (x₁ - s • b) = s • (mat g⁻¹ * x0 - mat g⁻¹ * b) := by
               rw [← hsx0, ← smul_sub, Matrix.mul_smul, Matrix.mul_sub]
          _ = s • (x0 + a) := by rw [e']; congr 1; abel
          _ = x₁ + s • a := by rw [smul_add, hsx0]
      have hkey : mat g⁻¹ * (eM v n - S * (b * r)) = eM v n + S * (a * r) := by
        rw [← D.right, hSx, hSx, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.sub_mul, ← Matrix.add_mul,
          ← Matrix.mul_assoc, e0]
      have hsk : ∀ p : Matrix (Fin n) (Fin n) (AE F E), sg v ϖ • (sg v (ϖ ^ k₀) • p) = s • p := fun _ => by
        rw [smul_smul, sg_mul]; dsimp [s, k]; rw [pow_succ']
      obtain ⟨q, hq, hq1⟩ := D.unit (sg v (ϖ ^ k₀) • (-(b * r))) (D.smul_mem _ (hϖO _) _ (neg_mem hβ))
      obtain ⟨q', hq', hq1'⟩ := D.unit (sg v (ϖ ^ k₀) • (a * r)) (D.smul_mem _ (hϖO _) _ hα)
      rw [hsk, smul_neg, ← sub_eq_add_neg, ← hSx] at hq1; rw [hsk, ← hSx] at hq1'
      have eL : ∀ x ∈ Λ, eM v n * x = x := fun x hx => by
        rw [Matrix.smul_mul, Matrix.one_mul, sg_one (D.at_mem x hx)]
      have eR : ∀ x : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) x → x * eM v n = x := fun _ hx => by
        rw [Matrix.mul_smul, Matrix.mul_one, sg_one hx]
      obtain ⟨c1, c2⟩ := cong_key_pk (s := S) (m := mat g⁻¹) (m' := mat g) hcomm hkey hgm hq1 hq1' (eL q hq) (eL q' hq')
        (eR _ (D.at_mem _ hα)) (eR _ (D.at_mem _ hβ)) (eR _ hg') (eR _ hg)
      simp only [hSx] at c1 c2
      exact ⟨hg, ⟨_, add_mem (sub_mem (neg_mem hβ) (D.mul_mem _ hα _ hq')) (hsΛ _ (D.mul_mem _ hβ _ (D.mul_mem _ hα _
        hq'))), c2⟩,
        ⟨_, add_mem (add_mem hα (D.mul_mem _ hβ _ hq)) (hsΛ _ (D.mul_mem _ hα _ (D.mul_mem _ hβ _ hq))), c1⟩⟩
  refine ⟨H, φ, ⟨hφS, hφ0, fun _ hg => Subgroup.subset_closure hg.1, fun g hg => (hsm g hg).2.2, ?_, hfix, hsep⟩,
    fun g hg => (hsm g hg).1⟩
  obtain ⟨O, hO, h1, hOg⟩ := D.nbhd k
  exact ⟨O, hO, h1, fun g hg hgO => by
    have hu := mem_UAt_of_locGrp_pk hg; exact ⟨hu, (hOg g hu hgO).1, (hOg g hu hgO).2⟩⟩
end UpperTheory.TP.BA
end
