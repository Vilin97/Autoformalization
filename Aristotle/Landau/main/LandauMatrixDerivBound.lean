/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 0f6845b7-3613-4003-80e9-66b9caa0edaf

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma landauMatrix_entry_fderiv_norm_bound
    {Ψ : ℝ → ℝ} (hΨ_diff : ContDiff ℝ 1 Ψ) (hΨ_bound : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ)
    (hΨ'_bound : ∃ CΨ', ∀ r, |deriv Ψ r| ≤ CΨ')
    (i j : Fin 3) :
    ∃ C, ∀ z : Fin 3 → ℝ,
      ‖fderiv ℝ (fun z => landauMatrix' Ψ z i j) z‖ ≤ C * (1 + ‖z‖) ^ 2

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib
import Aristotle.Landau.main.Defs

import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic


open MeasureTheory Matrix Finset BigOperators Real Filter

noncomputable section

-- Self-contained definitions (matching VML.normSq, VML.eucNorm, etc. from Defs.lean)
def normSq' (z : Fin 3 → ℝ) : ℝ := dotProduct z z

def eucNorm' (z : Fin 3 → ℝ) : ℝ := Real.sqrt (normSq' z)

def innerLandauMatrix' (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  normSq' z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - vecMulVec z z

def landauMatrix' (Ψ : ℝ → ℝ) (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Ψ (eucNorm' z) • innerLandauMatrix' z

/- Each entry of the Landau matrix has a quadratic derivative bound:
    ‖D_v A_{ij}(z)‖ ≤ C · (1 + ‖z‖)²

    Sketch: A_{ij}(z) = Ψ(‖z‖)(‖z‖²δ_{ij} - z_i z_j). For z ≠ 0:
    D_k A_{ij}(z) = Ψ'(‖z‖)(z_k/‖z‖)(‖z‖²δ_{ij} - z_i z_j)
                  + Ψ(‖z‖)(2z_k δ_{ij} - δ_{ik}z_j - z_i δ_{jk})
    First term: |Ψ'| ≤ CΨ', |z_k/‖z‖| ≤ 1, |‖z‖²δ_{ij} - z_i z_j| ≤ 2‖z‖² → bounded by 2CΨ'‖z‖²
    Second term: bounded by CΨ · 4‖z‖
    Total: ‖D A_{ij}(z)‖ ≤ (2CΨ' + 4CΨ)(1 + ‖z‖)²
    At z = 0: A_{ij}(0) = 0, so fderiv = 0, and bound = C ≥ 0. -/
noncomputable section AristotleLemmas

/-
The sup norm of z is less than or equal to the Euclidean norm of z.
-/
lemma norm_le_eucNorm' (z : Fin 3 → ℝ) : ‖z‖ ≤ eucNorm' z := by
  norm_num [ eucNorm' ];
  norm_num [ normSq', eucNorm' ] at *;
  norm_num [ dotProduct, Norm.norm ] at *;
  norm_num [ Fin.univ_succ ] at *;
  simp +zetaDelta at *;
  exact ⟨ Real.abs_le_sqrt ( by nlinarith ), Real.abs_le_sqrt ( by nlinarith ), Real.abs_le_sqrt ( by nlinarith ) ⟩

/-
The Euclidean norm is bounded by sqrt(3) times the sup norm.
-/
lemma eucNorm'_le_sqrt_three_norm (z : Fin 3 → ℝ) : eucNorm' z ≤ Real.sqrt 3 * ‖z‖ := by
  -- By definition of the Euclidean norm, we know that
  have h_def : eucNorm' z = Real.sqrt ((∑ i : Fin 3, z i ^ 2)) := by
    unfold eucNorm' normSq' dotProduct; norm_num [ Fin.sum_univ_three ] ; ring;
  -- By definition of the supremum norm, we know that
  have h_sup : ∀ i : Fin 3, z i ^ 2 ≤ ‖z‖ ^ 2 := by
    exact fun i => by nlinarith only [ abs_le.mp ( norm_le_pi_norm z i ) ] ;
  exact h_def.symm ▸ Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ 3 by norm_num ), show ( ∑ i : Fin 3, z i ^ 2 ) ≤ 3 * ‖z‖ ^ 2 by simpa using Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => h_sup i ] ⟩

/-
The Frechet derivative of normSq' at z, defined as a continuous linear map.
-/
def dNormSq (z : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun v => 2 * dotProduct z v
       map_add' := by
         -- The dot product is linear, so we can distribute the multiplication over addition.
         intros x y
         simp [dotProduct, add_mul, mul_add];
         rw [ ← mul_add, Finset.sum_add_distrib ]
       map_smul' := by
         simp +decide [ dotProduct, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ] } : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)

/-
Bound on the absolute value of normSq' z.
|normSq' z| = |sum z_i^2| <= sum |z_i|^2 <= sum ||z||^2 = 3 * ||z||^2.
-/
lemma normSq'_le_three_norm_sq (z : Fin 3 → ℝ) : |normSq' z| ≤ 3 * ‖z‖^2 := by
  unfold normSq';
  norm_num [ dotProduct ];
  rw [ abs_le ] ; constructor <;> norm_num [ Fin.sum_univ_three ] <;> nlinarith [ abs_le.mp ( show |z 0| ≤ ‖z‖ from by simpa using norm_le_pi_norm z 0 ), abs_le.mp ( show |z 1| ≤ ‖z‖ from by simpa using norm_le_pi_norm z 1 ), abs_le.mp ( show |z 2| ≤ ‖z‖ from by simpa using norm_le_pi_norm z 2 ) ] ;

/-
The Fréchet derivative of normSq' at z is dNormSq z.
Proof:
Expand `normSq' (z + h)` to get `normSq' z + 2 * dotProduct z h + normSq' h`.
Subtracting the value and the derivative leaves `normSq' h`.
We need to show `normSq' h` is `o(h)`.
`|normSq' h| <= 3 * ||h||^2`.
For `||h|| < c/3`, `3 * ||h||^2 <= 3 * (c/3) * ||h|| = c * ||h||`.
-/
lemma normSq'_hasFDerivAt (z : Fin 3 → ℝ) :
    HasFDerivAt normSq' (dNormSq z) z := by
      rw [ hasFDerivAt_iff_isLittleO_nhds_zero ];
      refine' Asymptotics.isLittleO_iff.2 _;
      intro ε hε;
      -- We'll use that ‖normSq' (z + x) - normSq' z - (dNormSq z) x‖ ≤ 3 * ‖x‖^2.
      have h_bound : ∀ x : Fin 3 → ℝ, ‖normSq' (z + x) - normSq' z - (dNormSq z) x‖ ≤ 3 * ‖x‖^2 := by
        intro x; exact (by
        convert normSq'_le_three_norm_sq x using 1 ; norm_num [ normSq', dNormSq ] ; ring;
        norm_num [ dotProduct_comm ]);
      filter_upwards [ Metric.ball_mem_nhds _ ( show 0 < ε / 3 by positivity ) ] with x hx using le_trans ( h_bound x ) ( by nlinarith [ norm_nonneg x, show ‖x‖ < ε / 3 by simpa using hx ] )

/-
Explicit formula for the entries of the inner Landau matrix.
-/
lemma innerLandauEntry_val (z : Fin 3 → ℝ) (i j : Fin 3) :
    innerLandauMatrix' z i j = normSq' z * (if i = j then 1 else 0) - z i * z j := by
      unfold innerLandauMatrix';
      fin_cases i <;> fin_cases j <;> norm_num [ Matrix.vecMulVec ]

/-
Bound on the entries of the inner Landau matrix.
If i = j, the entry is sum_{k != i} z_k^2, which is bounded by 2 * ||z||^2.
If i != j, the entry is -z_i * z_j, which is bounded by ||z||^2 <= 2 * ||z||^2.
-/
lemma innerLandauEntry_bound (z : Fin 3 → ℝ) (i j : Fin 3) :
    |innerLandauMatrix' z i j| ≤ 2 * ‖z‖^2 := by
      -- Let's expand the definition of innerLandauMatrix' at i and j.
      have h_inner : innerLandauMatrix' z i j = normSq' z * (if i = j then 1 else 0) - z i * z j := by
        exact?;
      by_cases hij : i = j <;> simp_all +decide [ abs_le ];
      · unfold normSq';
        norm_num [ dotProduct, Fin.sum_univ_three ];
        constructor <;> fin_cases j <;> nlinarith! [ abs_le.mp ( norm_le_pi_norm z 0 ), abs_le.mp ( norm_le_pi_norm z 1 ), abs_le.mp ( norm_le_pi_norm z 2 ) ];
      · nlinarith only [ abs_nonneg ( z i ), abs_nonneg ( z j ), show |z i| ≤ ‖z‖ from norm_le_pi_norm z i, show |z j| ≤ ‖z‖ from norm_le_pi_norm z j ]

/-
The derivative of the cross term z_i * z_j.
-/
def dCrossTerm (z : Fin 3 → ℝ) (i j : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun v => v i * z j + z i * v j
       map_add' := by intros; simp; ring
       map_smul' := by intros; simp; ring } : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)

/-
The Fréchet derivative of the cross term `z_i * z_j` is `dCrossTerm z i j`.
Proof: Use the product rule on the projection maps `z ↦ z i` and `z ↦ z j`. The derivative of a linear map is the map itself.
-/
lemma crossTerm_hasFDerivAt (z : Fin 3 → ℝ) (i j : Fin 3) :
    HasFDerivAt (fun z => z i * z j) (dCrossTerm z i j) z := by
      unfold dCrossTerm;
      rw [ hasFDerivAt_iff_isLittleO_nhds_zero ] ; norm_num [ mul_comm ] ; ring!; (
      refine' Asymptotics.isLittleO_iff.2 _;
      intro ε hε; filter_upwards [ Metric.ball_mem_nhds _ hε ] with x hx; by_cases hi : x i = 0 <;> by_cases hj : x j = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ; ring_nf ; (
      exact mul_le_mul ( le_trans ( norm_le_pi_norm x i ) hx.le ) ( norm_le_pi_norm x j ) ( by positivity ) ( by positivity ) |> le_trans ( by norm_num ) ;);)

/-
Definition of the derivative of `Ψ(‖z‖)` for `z ≠ 0`.
It is `v ↦ Ψ'(‖z‖) * (z · v) / ‖z‖`.
Linearity is established via LinearMap.toContinuousLinearMap.
-/
def dPsiNorm (Ψ : ℝ → ℝ) (z : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun v => (deriv Ψ (eucNorm' z)) * (dotProduct z v) * (eucNorm' z)⁻¹
       map_add' := by
         simp +decide [ mul_add, add_mul, Finset.sum_add_distrib ]
       map_smul' := by
         simp +decide [ mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ] } : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)

/-
Definition of the derivative of the Euclidean norm for `z ≠ 0`.
It is `v ↦ (z · v) / ‖z‖`.
Linearity is established via LinearMap.toContinuousLinearMap.
-/
def dEucNorm (z : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun v => dotProduct z v / eucNorm' z
       map_add' := by
         simp +decide [ div_add_div_same, dotProduct_add ]
       map_smul' := by
         simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, dotProduct_smul ] } : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)

/-
If z is not zero, then normSq' z is positive.
-/
lemma normSq'_pos {z : Fin 3 → ℝ} (hz : z ≠ 0) : 0 < normSq' z := by
  have h_pos : 0 < ∑ i, z i ^ 2 := by
    exact lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ( Ne.symm <| by contrapose! hz; ext i; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] );
  simpa [ sq, normSq' ] using h_pos

/-
The Fréchet derivative of `eucNorm'` at `z ≠ 0` is `dEucNorm z`.
Proof: Chain rule with `sqrt` and `normSq'`.
`eucNorm' z = sqrt (normSq' z)`.
Derivative is `(1 / (2 * sqrt (normSq' z))) * dNormSq z`.
`dNormSq z v = 2 * (z · v)`.
Result is `(z · v) / eucNorm' z`.
-/
lemma eucNorm'_hasFDerivAt {z : Fin 3 → ℝ} (hz : z ≠ 0) :
    HasFDerivAt eucNorm' (dEucNorm z) z := by
      convert HasFDerivAt.sqrt ( normSq'_hasFDerivAt z ) _ using 1;
      · ext; norm_num [ dEucNorm, dNormSq ] ; ring;
        rfl;
      · exact ne_of_gt ( normSq'_pos hz )

/-
Definition of the derivative of the inner Landau matrix entry.
It is `dNormSq z * delta_{ij} - dCrossTerm z`.
Linearity is established via LinearMap.toContinuousLinearMap.
-/
def dInnerLandauEntry (z : Fin 3 → ℝ) (i j : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun v => (2 * dotProduct z v) * (if i = j then 1 else 0) - (v i * z j + z i * v j)
       map_add' := by
         simp +decide [ mul_add, add_mul, Finset.mul_sum _ _ _, Finset.sum_add_distrib, dotProduct ] ; intros ; ring;
         split_ifs <;> ring
       map_smul' := by
         simp +decide [ mul_sub, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ];
         exact fun m x => by ring; } : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)

/-
The Fréchet derivative of the inner Landau matrix entry is `dInnerLandauEntry`.
Proof: It is `normSq' z * const - crossTerm z`.
Derivative is `dNormSq z * const - dCrossTerm z`.
This matches `dInnerLandauEntry`.
-/
lemma innerLandauEntry_hasFDerivAt (z : Fin 3 → ℝ) (i j : Fin 3) :
    HasFDerivAt (fun z => innerLandauMatrix' z i j) (dInnerLandauEntry z i j) z := by
      unfold dInnerLandauEntry innerLandauMatrix';
      convert HasFDerivAt.sub ( HasFDerivAt.smul ( normSq'_hasFDerivAt z ) ( hasFDerivAt_const _ _ ) ) ( crossTerm_hasFDerivAt z i j ) using 1 ; norm_num [ Matrix.vecMulVec ] ; ring!;
      ext; simp [dNormSq, dCrossTerm]; ring; aesop;

/-
Definition of the derivative of the Landau matrix entry.
It is 0 if z=0, otherwise given by the product rule.
-/
def dLandauEntry (Ψ : ℝ → ℝ) (z : Fin 3 → ℝ) (i j : Fin 3) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  if h : z = 0 then 0 else
  (innerLandauMatrix' z i j) • (dPsiNorm Ψ z) + (Ψ (eucNorm' z)) • (dInnerLandauEntry z i j)

/-
Cauchy-Schwarz inequality for `dotProduct` and `eucNorm'`.
`|z · v| ≤ ‖z‖_2 * ‖v‖_2`.
-/
lemma abs_dotProduct_le_eucNorm'_mul_eucNorm' (z v : Fin 3 → ℝ) :
    |dotProduct z v| ≤ eucNorm' z * eucNorm' v := by
      -- By the Cauchy-Schwarz inequality, we have $|z \cdot v| \leq \|z\|_2 \|v\|_2$.
      have h_cauchy_schwarz : ∀ (z v : EuclideanSpace ℝ (Fin 3)), abs (inner ℝ z v) ≤ ‖z‖ * ‖v‖ := by
        exact fun z v => abs_real_inner_le_norm z v;
      convert h_cauchy_schwarz z v using 1 ; norm_num [ EuclideanSpace.norm_eq, dotProduct ] ; ring;
      · norm_num [ Fin.sum_univ_three, inner ] ; ring!;
      · norm_num [ Norm.norm, eucNorm' ];
        norm_num [ ← Real.sqrt_eq_rpow, normSq' ];
        norm_num [ sq, dotProduct ]

/-
If z is not zero, then eucNorm' z is positive.
-/
lemma eucNorm'_pos {z : Fin 3 → ℝ} (hz : z ≠ 0) : 0 < eucNorm' z := by
  unfold eucNorm'
  exact Real.sqrt_pos.mpr (normSq'_pos hz)

/-
eucNorm' is always non-negative.
-/
lemma eucNorm'_nonneg (z : Fin 3 → ℝ) : 0 ≤ eucNorm' z := by
  unfold eucNorm'
  exact Real.sqrt_nonneg _

/-
Bound on the operator norm of `dPsiNorm`.
`‖dPsiNorm Ψ z‖ ≤ √3 * |Ψ'(‖z‖_2)|`.
Proof uses Cauchy-Schwarz for `dotProduct` and the bound `‖v‖_2 ≤ √3 * ‖v‖_∞`.
-/
lemma dPsiNorm_bound {Ψ : ℝ → ℝ} {z : Fin 3 → ℝ} (hz : z ≠ 0) :
    ‖dPsiNorm Ψ z‖ ≤ Real.sqrt 3 * |deriv Ψ (eucNorm' z)| := by
      refine' csInf_le _ _ <;> norm_num [ dPsiNorm ] ; ring_nf ; norm_num [ Real.sqrt_le_iff ] ; (
      exact ⟨ 0, fun c hc => hc.1 ⟩);
      -- Apply the bound on the Euclidean norm of x and the Cauchy-Schwarz inequality.
      have h_bound : ∀ x : Fin 3 → ℝ, |dotProduct z x| ≤ eucNorm' z * Real.sqrt 3 * ‖x‖ := by
        intro x
        have h_cauchy_schwarz : |dotProduct z x| ≤ eucNorm' z * eucNorm' x := by
          exact?
        have h_eucNorm'_le_sqrt_three_norm : eucNorm' x ≤ Real.sqrt 3 * ‖x‖ := by
          exact?
        exact le_trans h_cauchy_schwarz (by
        simpa only [ mul_assoc ] using mul_le_mul_of_nonneg_left h_eucNorm'_le_sqrt_three_norm ( eucNorm'_nonneg z ));
      intro x; rw [ abs_of_nonneg ( eucNorm'_nonneg z ) ] ; convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( h_bound x ) ( abs_nonneg ( deriv Ψ ( eucNorm' z ) ) ) ) ( inv_nonneg.mpr ( eucNorm'_nonneg z ) ) using 1 ; ring;
      rw [ mul_inv_cancel_right₀ ( ne_of_gt ( eucNorm'_pos hz ) ) ]

/-
For `z ≠ 0`, the derivative of `landauMatrix'` is `dLandauEntry`.
Proof: Product rule.
Derivative of `Ψ(‖z‖)` is `dPsiNorm`.
Derivative of `innerLandauMatrix'` is `dInnerLandauEntry`.
Formula matches `dLandauEntry`.
-/
lemma landauEntry_hasFDerivAt_of_ne_zero
    {Ψ : ℝ → ℝ} (hΨ_diff : ContDiff ℝ 1 Ψ) (z : Fin 3 → ℝ) (hz : z ≠ 0) (i j : Fin 3) :
    HasFDerivAt (fun z => landauMatrix' Ψ z i j) (dLandauEntry Ψ z i j) z := by
      unfold landauMatrix' dLandauEntry;
      split_ifs ; simp_all +decide [ hasFDerivAt_iff_tendsto ];
      -- Apply the product rule for Fréchet derivatives.
      have h_prod_rule : HasFDerivAt (fun z => Ψ (eucNorm' z)) (dPsiNorm Ψ z) z ∧ HasFDerivAt (fun z => innerLandauMatrix' z i j) (dInnerLandauEntry z i j) z := by
        refine' ⟨ _, innerLandauEntry_hasFDerivAt z i j ⟩;
        convert HasFDerivAt.comp z ( hΨ_diff.differentiable le_rfl |> Differentiable.differentiableAt |> DifferentiableAt.hasFDerivAt ) ( eucNorm'_hasFDerivAt hz ) using 1;
        ext; simp [dPsiNorm, dEucNorm];
        ring!;
      convert h_prod_rule.1.smul h_prod_rule.2 using 1 ; ext ; norm_num ; ring!;

/-
Bound for `dLandauEntry` when `z ≠ 0`.
It is bounded by `C * (1 + ‖z‖)^2`.
Proof combines bounds for `innerLandauMatrix'`, `dPsiNorm`, `Ψ`, and `dInnerLandauEntry`.
`|inner| * ‖dPsiNorm‖ ≤ 2‖z‖² * √3 CΨ'`.
`|Ψ| * ‖dInner‖ ≤ CΨ * 4‖z‖`.
Sum is `≤ C * (1 + ‖z‖)²`.
-/
lemma dLandauEntry_bound_of_ne_zero
    {Ψ : ℝ → ℝ} (hΨ_bound : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ)
    (hΨ'_bound : ∃ CΨ', ∀ r, |deriv Ψ r| ≤ CΨ')
    (z : Fin 3 → ℝ) (hz : z ≠ 0) (i j : Fin 3) :
    ∃ C, ‖dLandauEntry Ψ z i j‖ ≤ C * (1 + ‖z‖)^2 := by
      exact ⟨ ‖dLandauEntry Ψ z i j‖ / ( 1 + ‖z‖ ) ^ 2, by rw [ div_mul_cancel₀ _ ( by positivity ) ] ⟩

end AristotleLemmas

set_option maxHeartbeats 1600000 in
lemma landauMatrix_entry_fderiv_norm_bound
    {Ψ : ℝ → ℝ} (hΨ_diff : ContDiff ℝ 1 Ψ) (hΨ_bound : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ)
    (hΨ'_bound : ∃ CΨ', ∀ r, |deriv Ψ r| ≤ CΨ')
    (i j : Fin 3) :
    ∃ C, ∀ z : Fin 3 → ℝ,
      ‖fderiv ℝ (fun z => landauMatrix' Ψ z i j) z‖ ≤ C * (1 + ‖z‖) ^ 2 := by
  -- We prove the bound by cases on whether z is zero or not. If z ≠ 0, the derivative is given by `dLandauEntry`, and we have proved a bound for it in `dLandauEntry_bound_of_ne_zero`.
  by_cases h_zero : ∃ C, ∀ z : Fin 3 → ℝ, z ≠ 0 → ‖fderiv ℝ (fun z => landauMatrix' Ψ z i j) z‖ ≤ C * (1 + ‖z‖) ^ 2;
  · obtain ⟨ C, hC ⟩ := h_zero;
    use Max.max C ‖fderiv ℝ ( fun z => landauMatrix' Ψ z i j ) 0‖;
    intro z; by_cases hz : z = 0 <;> simp_all +decide [ mul_assoc ] ;
    exact le_trans ( hC z hz ) ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( sq_nonneg _ ) );
  · obtain ⟨C, hC⟩ : ∃ C, ∀ z : Fin 3 → ℝ, z ≠ 0 → ‖fderiv ℝ (fun z => landauMatrix' Ψ z i j) z‖ ≤ C * (1 + ‖z‖) ^ 2 := by
      -- By combining the bounds for the derivatives of the individual terms, we can find a suitable constant C.
      obtain ⟨C₁, hC₁⟩ : ∃ C₁, ∀ z : Fin 3 → ℝ, z ≠ 0 → ‖(innerLandauMatrix' z i j) • (dPsiNorm Ψ z)‖ ≤ C₁ * (1 + ‖z‖) ^ 2 := by
        obtain ⟨C₁, hC₁⟩ : ∃ C₁, ∀ z : Fin 3 → ℝ, z ≠ 0 → |innerLandauMatrix' z i j| ≤ C₁ * (1 + ‖z‖) ^ 2 := by
          use 2; intro z hz; exact le_trans ( innerLandauEntry_bound z i j ) ( by nlinarith [ norm_nonneg z ] ) ;
        obtain ⟨C₂, hC₂⟩ : ∃ C₂, ∀ z : Fin 3 → ℝ, z ≠ 0 → ‖dPsiNorm Ψ z‖ ≤ C₂ := by
          exact ⟨ Real.sqrt 3 * hΨ'_bound.choose, fun z hz => le_trans ( dPsiNorm_bound hz ) ( mul_le_mul_of_nonneg_left ( hΨ'_bound.choose_spec _ ) ( Real.sqrt_nonneg _ ) ) ⟩ ;
        use C₁ * C₂
        intro z hz
        simp [hC₁, hC₂] at *; (
        simpa only [ norm_smul, mul_assoc, mul_comm, mul_left_comm ] using mul_le_mul ( hC₁ z hz ) ( hC₂ z hz ) ( by positivity ) ( by nlinarith [ hC₁ z hz, hC₂ z hz, norm_nonneg z, abs_nonneg ( innerLandauMatrix' z i j ) ] ) |> le_trans <| by ring_nf; norm_num;); -- Apply the bounds for the individual terms. (MOVED TO NEXT STEP)
      obtain ⟨C₂, hC₂⟩ : ∃ C₂, ∀ z : Fin 3 → ℝ, z ≠ 0 → ‖(Ψ (eucNorm' z)) • (dInnerLandauEntry z i j)‖ ≤ C₂ * (1 + ‖z‖) ^ 2 := by
        -- By combining the bounds for the derivatives of the individual terms, we can find a suitable constant C₂.
        obtain ⟨C₂, hC₂⟩ : ∃ C₂, ∀ z : Fin 3 → ℝ, z ≠ 0 → ‖dInnerLandauEntry z i j‖ ≤ C₂ * (1 + ‖z‖) := by
          use 4;
          intro z hz; specialize hC₁ z hz; specialize h_zero; simp_all +decide [ dInnerLandauEntry ] ; ring_nf at *; (
          refine' ContinuousLinearMap.opNorm_le_bound _ _ _ <;> norm_num [ dotProduct ] ; ring_nf ; (
          positivity);
          intro x; split_ifs <;> norm_num [ Fin.sum_univ_three ] <;> ring_nf ; (
          fin_cases i <;> fin_cases j <;> simp +decide at * <;> ring_nf <;> norm_num [ abs_le ] at * <;> try linarith! [ abs_le.mp ( show |z 0| ≤ ‖z‖ from by simpa using norm_le_pi_norm z 0 ), abs_le.mp ( show |z 1| ≤ ‖z‖ from by simpa using norm_le_pi_norm z 1 ), abs_le.mp ( show |z 2| ≤ ‖z‖ from by simpa using norm_le_pi_norm z 2 ), abs_le.mp ( show |x 0| ≤ ‖x‖ from by simpa using norm_le_pi_norm x 0 ), abs_le.mp ( show |x 1| ≤ ‖x‖ from by simpa using norm_le_pi_norm x 1 ), abs_le.mp ( show |x 2| ≤ ‖x‖ from by simpa using norm_le_pi_norm x 2 ) ] ;
          · constructor <;> nlinarith [ abs_le.mp ( show |z 1| ≤ ‖z‖ from by simpa using norm_le_pi_norm z 1 ), abs_le.mp ( show |z 2| ≤ ‖z‖ from by simpa using norm_le_pi_norm z 2 ), abs_le.mp ( show |x 1| ≤ ‖x‖ from by simpa using norm_le_pi_norm x 1 ), abs_le.mp ( show |x 2| ≤ ‖x‖ from by simpa using norm_le_pi_norm x 2 ), norm_nonneg z, norm_nonneg x ] ;
          · constructor <;> nlinarith [ abs_le.mp ( show |z 0| ≤ ‖z‖ from by simpa using norm_le_pi_norm z 0 ), abs_le.mp ( show |z 2| ≤ ‖z‖ from by simpa using norm_le_pi_norm z 2 ), abs_le.mp ( show |x 0| ≤ ‖x‖ from by simpa using norm_le_pi_norm x 0 ), abs_le.mp ( show |x 2| ≤ ‖x‖ from by simpa using norm_le_pi_norm x 2 ), norm_nonneg z, norm_nonneg x ] ;
          · constructor <;> nlinarith! [ abs_le.mp ( show |z 0| ≤ ‖z‖ from by simpa using norm_le_pi_norm z 0 ), abs_le.mp ( show |z 1| ≤ ‖z‖ from by simpa using norm_le_pi_norm z 1 ), abs_le.mp ( show |z 2| ≤ ‖z‖ from by simpa using norm_le_pi_norm z 2 ), abs_le.mp ( show |x 0| ≤ ‖x‖ from by simpa using norm_le_pi_norm x 0 ), abs_le.mp ( show |x 1| ≤ ‖x‖ from by simpa using norm_le_pi_norm x 1 ), abs_le.mp ( show |x 2| ≤ ‖x‖ from by simpa using norm_le_pi_norm x 2 ) ] ;);
          refine' abs_le.mpr ⟨ _, _ ⟩ <;> nlinarith only [ abs_le.mp ( show |x i| ≤ ‖x‖ from by simpa using norm_le_pi_norm x i ), abs_le.mp ( show |z j| ≤ ‖z‖ from by simpa using norm_le_pi_norm z j ), abs_le.mp ( show |z i| ≤ ‖z‖ from by simpa using norm_le_pi_norm z i ), abs_le.mp ( show |x j| ≤ ‖x‖ from by simpa using norm_le_pi_norm x j ), show 0 ≤ ‖z‖ * ‖x‖ by positivity, show 0 ≤ ‖x‖ by positivity ] ;);
        generalize_proofs at *; exact ⟨hΨ_bound.choose * C₂, fun z hz => by
          rw [ norm_smul, mul_assoc ];
          exact mul_le_mul ( hΨ_bound.choose_spec _ ) ( le_trans ( hC₂ z hz ) ( mul_le_mul_of_nonneg_left ( by nlinarith [ norm_nonneg z ] ) ( show 0 ≤ C₂ by exact le_of_not_gt fun h => by have := hC₂ z hz; nlinarith [ norm_nonneg z, norm_nonneg ( dInnerLandauEntry z i j ) ] ) ) ) ( by positivity ) ( by linarith [ abs_le.mp ( hΨ_bound.choose_spec ( eucNorm' z ) ) ] )⟩;
      use C₁ + C₂;
      intro z hz
      have h_deriv : fderiv ℝ (fun z => landauMatrix' Ψ z i j) z = (innerLandauMatrix' z i j) • (dPsiNorm Ψ z) + (Ψ (eucNorm' z)) • (dInnerLandauEntry z i j) := by
        convert HasFDerivAt.fderiv ( landauEntry_hasFDerivAt_of_ne_zero hΨ_diff z hz i j ) using 1
        generalize_proofs at *; (
        unfold dLandauEntry; aesop;) -- Apply the triangle inequality to the sum of the derivatives.
      rw [h_deriv] at *; (
      exact le_trans ( norm_add_le _ _ ) ( by linarith [ hC₁ z hz, hC₂ z hz ] ) ;); -- Apply the triangle inequality to the sum of the derivatives.;
    exact False.elim <| h_zero ⟨ C, hC ⟩

-- Bridge: show standalone defs equal VML defs
lemma normSq'_eq_VML : normSq' = VML.normSq := rfl
lemma eucNorm'_eq_VML : eucNorm' = VML.eucNorm := rfl
lemma innerLandauMatrix'_eq_VML : innerLandauMatrix' = VML.innerLandauMatrix := rfl
lemma landauMatrix'_eq_VML : landauMatrix' = VML.landauMatrix := rfl

-- Aristotle-proved: |A_{ij}(z)| ≤ C * ‖z‖²
set_option maxHeartbeats 800000 in
lemma landauMatrix_entry_abs_bound
    {Ψ : ℝ → ℝ} (hΨ_bound : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ)
    (i j : Fin 3) :
    ∃ C, ∀ z : Fin 3 → ℝ, |landauMatrix' Ψ z i j| ≤ C * ‖z‖ ^ 2 := by
  have h_def : ∀ z : Fin 3 → ℝ, |landauMatrix' Ψ z i j| = |Ψ (eucNorm' z)| * |innerLandauMatrix' z i j| := by
    unfold landauMatrix' innerLandauMatrix' ; aesop;
  have h_inner_bound : ∀ z : Fin 3 → ℝ, |innerLandauMatrix' z i j| ≤ 2 * eucNorm' z^2 := by
    unfold innerLandauMatrix' eucNorm' normSq';
    intro z; norm_num [ Matrix.vecMulVec ] ; ring_nf;
    fin_cases i <;> fin_cases j <;> simp +decide [ dotProduct ] <;> ring_nf <;> norm_num [ Real.sqrt_sq_eq_abs ];
    all_goals rw [ Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ] ; norm_num [ Fin.sum_univ_three ] ; ring_nf ; norm_num [ abs_le ] ;
    any_goals constructor <;> nlinarith [ sq_nonneg ( |z 0| - |z 1| ), sq_nonneg ( |z 0| - |z 2| ), sq_nonneg ( |z 1| - |z 2| ), abs_mul_abs_self ( z 0 ), abs_mul_abs_self ( z 1 ), abs_mul_abs_self ( z 2 ) ] ;
    all_goals nlinarith [ sq_nonneg ( |z 0| - |z 1| ), sq_nonneg ( |z 0| - |z 2| ), sq_nonneg ( |z 1| - |z 2| ), abs_mul_abs_self ( z 0 ), abs_mul_abs_self ( z 1 ), abs_mul_abs_self ( z 2 ) ] ;
  obtain ⟨CΨ, hCΨ⟩ : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ := hΨ_bound
  use CΨ * 2 * 3^2
  intro z
  have : eucNorm' z^2 ≤ 3 * ‖z‖^2 := by
    unfold eucNorm' normSq';
    norm_num [ dotProduct, Norm.norm ];
    rw [ Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => mul_self_nonneg _ ] ; norm_num [ Fin.sum_univ_three ] ; nlinarith! [ abs_le.mp ( show |z 0| ≤ ( Finset.univ.sup fun b => ‖z b‖₊ ) from mod_cast Finset.le_sup ( f := fun b => ‖z b‖₊ ) ( Finset.mem_univ 0 ) ), abs_le.mp ( show |z 1| ≤ ( Finset.univ.sup fun b => ‖z b‖₊ ) from mod_cast Finset.le_sup ( f := fun b => ‖z b‖₊ ) ( Finset.mem_univ 1 ) ), abs_le.mp ( show |z 2| ≤ ( Finset.univ.sup fun b => ‖z b‖₊ ) from mod_cast Finset.le_sup ( f := fun b => ‖z b‖₊ ) ( Finset.mem_univ 2 ) ) ] ;
  simp [h_def, h_inner_bound, this];
  nlinarith [ abs_nonneg ( Ψ ( eucNorm' z ) ), abs_nonneg ( innerLandauMatrix' z i j ), hCΨ ( eucNorm' z ), h_inner_bound z ]

namespace VML

/-- Quadratic derivative bound on Landau matrix entries (proved by Aristotle).
    ‖D_v A_{ij}(z)‖ ≤ C · (1 + ‖z‖)² -/
lemma landauMatrix_entry_fderiv_norm_bound'
    {Ψ : ℝ → ℝ} (hΨ_diff : ContDiff ℝ 1 Ψ) (hΨ_bound : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ)
    (hΨ'_bound : ∃ CΨ', ∀ r, |deriv Ψ r| ≤ CΨ')
    (i j : Fin 3) :
    ∃ C, ∀ z : Fin 3 → ℝ,
      ‖fderiv ℝ (fun z => landauMatrix Ψ z i j) z‖ ≤ C * (1 + ‖z‖) ^ 2 := by
  have h := landauMatrix_entry_fderiv_norm_bound hΨ_diff hΨ_bound hΨ'_bound i j
  rwa [landauMatrix'_eq_VML] at h

/-- Quadratic bound on absolute value of Landau matrix entries (proved by Aristotle).
    |A_{ij}(z)| ≤ C · ‖z‖² -/
lemma landauMatrix_entry_abs_bound'
    {Ψ : ℝ → ℝ} (hΨ_bound : ∃ CΨ, ∀ r, |Ψ r| ≤ CΨ)
    (i j : Fin 3) :
    ∃ C, ∀ z : Fin 3 → ℝ, |landauMatrix Ψ z i j| ≤ C * ‖z‖ ^ 2 := by
  have h := landauMatrix_entry_abs_bound hΨ_bound i j
  rwa [landauMatrix'_eq_VML] at h

end VML