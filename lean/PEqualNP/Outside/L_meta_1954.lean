import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_1954_aux

private theorem gateDegree_pos {g : Gate} {a b : ℕ} {degrees : List ℕ}
    (hinputs : g.inputs = [a, b]) (ha : 0 < degrees.getD a 0) :
    0 < g.lineDegree degrees := by
  unfold Gate.lineDegree
  split
  · simp only [hinputs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  · simpa [hinputs] using ha.trans_le
      (le_max_left (degrees.getD a 0) (degrees.getD b 0))

private theorem foldDegree_pos (gates : List Gate) (left right : List ℕ)
    (hlen : right.length = left.length)
    (hshape : ∀ j (hj : j < gates.length), gates[j].inputs.length = 2)
    (hreads : ∀ j (hj : j < gates.length), ∀ i ∈ gates[j].inputs, i < left.length + j)
    (hpos : ∀ i < left.length, 0 < left.getD i 0 ∨ 0 < right.getD i 0) :
    ∀ i < left.length + gates.length,
      0 < (gates.foldl (fun d g => d ++ [g.lineDegree d]) left).getD i 0 ∨
      0 < (gates.foldl (fun d g => d ++ [g.lineDegree d]) right).getD i 0 := by
  induction gates generalizing left right with
  | nil => simpa using hpos
  | cons g gates ih =>
    have hgshape : g.inputs.length = 2 := hshape 0 (by simp)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hgshape
    have ha : a < left.length := by
      simpa using hreads 0 (by simp) a (by change a ∈ g.inputs; simp [hab])
    have hgpos : 0 < g.lineDegree left ∨ 0 < g.lineDegree right :=
      (hpos a ha).imp (gateDegree_pos hab) (gateDegree_pos hab)
    have hnext : ∀ i < (left ++ [g.lineDegree left]).length,
        0 < (left ++ [g.lineDegree left]).getD i 0 ∨
        0 < (right ++ [g.lineDegree right]).getD i 0 := by
      intro i hi
      by_cases hli : i < left.length
      · rw [List.getD_append _ _ _ _ hli, List.getD_append _ _ _ _ (by rwa [hlen])]
        exact hpos i hli
      · simp only [List.length_append, List.length_singleton] at hi
        have heq : i = left.length := by omega
        subst i
        rw [List.getD_append_right _ _ _ _ (le_refl _),
            List.getD_append_right _ _ _ _ (by rw [hlen])]
        simpa [hlen] using hgpos
    have hshape' : ∀ j (hj : j < gates.length), gates[j].inputs.length = 2 := by
      intro j hj
      exact hshape (j + 1) (by simpa)
    have hreads' : ∀ j (hj : j < gates.length), ∀ i ∈ gates[j].inputs,
        i < (left ++ [g.lineDegree left]).length + j := by
      intro j hj i hi
      have h := hreads (j + 1) (by simpa) i hi
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using h
    intro i hi
    simp only [List.foldl_cons]
    exact ih _ _ (by simp [hlen]) hshape' hreads' hnext i (by
      simp only [List.length_append, List.length_cons] at hi ⊢
      omega)

private theorem inputDegree {N i : ℕ} (marked : Finset ℕ) (hi : i < N + N) :
    ((List.range (N + N)).map (fun j => if j ∈ marked then 1 else 0)).getD i 0 =
      if i ∈ marked then 1 else 0 := by
  have h : i < ((List.range (N + N)).map (fun j => if j ∈ marked then 1 else 0)).length := by
    simpa using hi
  rw [List.getD_eq_getElem _ _ h]
  simp

private theorem wireDegree_pos (N : ℕ) (C : Circuit)
    (hshape : ∀ g ∈ C.gates, g.inputs.length = 2) (hreads : ReadsBack (N + N) C)
    {i : ℕ} (hi : i < N + N + C.gates.length) :
    0 < (C.lineDegrees (N + N) (Finset.range N)).getD i 0 ∨
    0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0 := by
  let left := (List.range (N + N)).map fun j => if j ∈ Finset.range N then 1 else 0
  let right := (List.range (N + N)).map fun j => if j ∈ Finset.Ico N (N + N) then 1 else 0
  have hlen : left.length = N + N := by simp [left]
  have hshape' : ∀ j (hj : j < C.gates.length), C.gates[j].inputs.length = 2 := by
    intro j hj
    exact hshape _ (List.getElem_mem hj)
  have hreads' : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs,
      i < left.length + j := by
    intro j hj w hw
    rw [hlen]
    exact hreads j hj w (by simpa only [gateAt, List.getD_eq_getElem _ _ hj] using hw)
  have hbase : ∀ j < left.length, 0 < left.getD j 0 ∨ 0 < right.getD j 0 := by
    intro j hj
    rw [hlen] at hj
    simp only [left, right, inputDegree _ hj]
    by_cases h : j < N
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [Finset.mem_Ico, Nat.le_of_not_gt h, hj])
  exact foldDegree_pos C.gates left right (by simp [left, right]) hshape' hreads' hbase i
    (by simpa [hlen] using hi)

private theorem threeCards {A B D U : Set ℕ} (hU : U.Finite)
    (hA : A ⊆ U) (hB : B ⊆ U) (hD : D ⊆ U)
    (hAB : Disjoint A B) (hAD : Disjoint A D) (hBD : Disjoint B D) :
    A.ncard + B.ncard + D.ncard ≤ U.ncard := by
  have hunion : Disjoint (A ∪ B) D := disjoint_sup_left.mpr ⟨hAD, hBD⟩
  have h := Set.ncard_le_ncard (Set.union_subset (Set.union_subset hA hB) hD) hU
  rwa [Set.ncard_union_eq hunion ((hU.subset hA).union (hU.subset hB)) (hU.subset hD),
    Set.ncard_union_eq hAB (hU.subset hA) (hU.subset hB)] at h

end PEqualNP.Outside.L_meta_1954_aux

open scoped BigOperators
open PEqualNP.Outside.L_meta_1954_aux

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_1954 :
    (∀ (N230 : ℕ) (C230 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g230 ∈ C230.gates, (g230.op =
    PEqualNP.CircuitLowerBounds.GateOp.and ∨ g230.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g230.inputs.length =
    2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N230 + N230) C230) → (∀ j230x2 < C230.gates.length,
    (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i230x2
    ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).inputs, (C230.lineDegrees (N230 + N230) (Finset.Ico
    N230 (N230 + N230))).getD i230x2 0 = 0) ∨ (∀ h230 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230
    j230x2).inputs, (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD h230 0 = 0)) →
    PEqualNP.MetaComplexity.circuitFun (N230 + N230) C230 (Fin.append (fun u230 : Fin N230 => true) (fun u230x1 :
    Fin N230 => false)) = false → ∀ mixed230 : ℕ → Prop, mixed230 = (fun i230 : ℕ => 0 < (C230.lineDegrees (N230 +
    N230) (Finset.range N230)).getD i230 0 ∧ 0 < (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 +
    N230))).getD i230 0) → ∀ cone230 : ℕ → Prop, cone230 = (fun j230 : ℕ => j230 < C230.gates.length ∧ mixed230
    (N230 + N230 + j230) ∧ Relation.ReflTransGen (fun a230 b230 : ℕ => a230 < b230 ∧ ∃ f230 : Fin C230.gates.length,
    b230 = N230 + N230 + f230.val ∧ a230 ∈ (C230.gates.get f230).inputs) (N230 + N230 + j230) C230.output) → (∀
    j230x1 : ℕ, cone230 j230x1 → (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x1).op =
    PEqualNP.CircuitLowerBounds.GateOp.or → ∀ i230x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230
    j230x1).inputs, 0 < (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230x1 0) ∧ Set.ncard
    {j230x3 : ℕ | cone230 j230x3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x3).op =
    PEqualNP.CircuitLowerBounds.GateOp.or} + Set.ncard {j230x4 : ℕ | cone230 j230x4} = Set.ncard {js230 : ℕ × ℕ |
    cone230 js230.1 ∧ js230.2 < 2 ∧ (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230.1).inputs.getD js230.2 0) 0 = 0} + Set.ncard {js230x1 :
    ℕ × ℕ | cone230 js230x1.1 ∧ js230x1.2 < 2 ∧ mixed230 ((PEqualNP.MetaComplexity.NestedCover.gateAt C230
    js230x1.1).inputs.getD js230x1.2 0)} ∧ Set.ncard {j230x5 : ℕ | cone230 j230x5} ≤ Set.ncard {js230x2 : ℕ × ℕ |
    cone230 js230x2.1 ∧ js230x2.2 < 2 ∧ mixed230 ((PEqualNP.MetaComplexity.NestedCover.gateAt C230
    js230x2.1).inputs.getD js230x2.2 0)} + 1) → (∀ (N231 : ℕ) (I231 : Fin N231 → Fin N231 → Prop) [DecidableRel
    I231] (C231 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g231 ∈ C231.gates, (g231.op =
    PEqualNP.CircuitLowerBounds.GateOp.and ∨ g231.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g231.inputs.length =
    2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N231 + N231) C231) → (∀ j231 < C231.gates.length,
    (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i231 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231
    (N231 + N231))).getD i231 0 = 0) ∨ (∀ h231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs,
    (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231 0 = 0)) → (∀ p231 p231x1 w231 w231x1 : Fin N231,
    p231 ≠ p231x1 → w231 ≠ w231x1 → I231 p231 w231 → I231 p231x1 w231 → I231 p231 w231x1 → I231 p231x1 w231x1 →
    False) → (∃ p231x2 w231x2 : Fin N231, I231 p231x2 w231x2) → (∀ p231x3 w231x3 : Fin N231, I231 p231x3 w231x3 →
    PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append (fun a231 : Fin N231 => decide (a231 =
    p231x3)) (fun a231x1 : Fin N231 => decide (a231x1 = w231x3))) = true) → (∀ x231 y231 : Fin N231 → Bool,
    (Finset.univ.filter (fun l231 : Fin N231 => y231 l231 = true)).card ≤ 1 → (¬ ∃ p231x4 w231x4 : Fin N231, I231
    p231x4 w231x4 ∧ x231 p231x4 = true ∧ y231 w231x4 = true) → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231
    (Fin.append x231 y231) = false) → ∀ mixed231 : ℕ → Prop, mixed231 = (fun i231x1 : ℕ => 0 < (C231.lineDegrees
    (N231 + N231) (Finset.range N231)).getD i231x1 0 ∧ 0 < (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 +
    N231))).getD i231x1 0) → ∀ cone231 : ℕ → Prop, cone231 = (fun j231x1 : ℕ => j231x1 < C231.gates.length ∧
    mixed231 (N231 + N231 + j231x1) ∧ Relation.ReflTransGen (fun a231x2 b231 : ℕ => a231x2 < b231 ∧ ∃ f231 : Fin
    C231.gates.length, b231 = N231 + N231 + f231.val ∧ a231x2 ∈ (C231.gates.get f231).inputs) (N231 + N231 + j231x1)
    C231.output) → ∀ gok231 : (Fin N231 → Bool) → ℕ → Prop, gok231 = (fun (x231x1 : Fin N231 → Bool) (j231x2 : ℕ) =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i231x2 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico
    N231 (N231 + N231))).getD i231x2 0 = 0 ∧ (C231.wires (List.ofFn (Fin.append x231x1 (fun u231 : Fin N231 =>
    false)))).getD i231x2 false = true) → ∀ step231 : (Fin N231 → Bool) → ℕ → ℕ → Prop, step231 = (fun (x231x2 : Fin
    N231 → Bool) (j231x3 j231x4 : ℕ) => cone231 j231x4 ∧ N231 + N231 + j231x3 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x4).inputs ∧ gok231 x231x2 j231x4) → ∀ lvx231 : (Fin N231 →
    Bool) → ℕ → Prop, lvx231 = (fun (x231x3 : Fin N231 → Bool) (j231x5 : ℕ) => cone231 j231x5 ∧ gok231 x231x3 j231x5
    ∧ ∃ j231x6 : ℕ, N231 + N231 + j231x6 = C231.output ∧ Relation.ReflTransGen (step231 x231x3) j231x5 j231x6) → ∀
    slot231 : ℕ → ℕ → Prop, slot231 = (fun h231x1 j231x7 : ℕ => cone231 j231x7 ∧ h231x1 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x7).inputs ∧ (C231.lineDegrees (N231 + N231) (Finset.range
    N231)).getD h231x1 0 = 0) → ∀ ap231 : ℕ → Fin N231 → Prop, ap231 = (fun (h231x2 : ℕ) (p231x5 : Fin N231) => ∃
    j231x8 : ℕ, slot231 h231x2 j231x8 ∧ lvx231 (fun a231x3 : Fin N231 => decide (a231x3 = p231x5)) j231x8) → ∀ lh231
    : ℕ → Fin N231 → Prop, lh231 = (fun (h231x3 : ℕ) (w231x5 : Fin N231) => (C231.wires (List.ofFn (Fin.append (fun
    u231x1 : Fin N231 => false) (fun a231x4 : Fin N231 => decide (a231x4 = w231x5))))).getD h231x3 false = true) → ∀
    lpw231 : ℕ → Fin N231 → Prop, lpw231 = (fun (h231x4 : ℕ) (w231x6 : Fin N231) => ∀ w231x7 : Fin N231, lh231
    h231x4 w231x7 ↔ w231x7 = w231x6) → ∀ ppw231 : ℕ → Fin N231 → Prop, ppw231 = (fun (h231x5 : ℕ) (p231x6 : Fin
    N231) => (∃ w231x8 w231x9 : Fin N231, w231x8 ≠ w231x9 ∧ lh231 h231x5 w231x8 ∧ lh231 h231x5 w231x9) ∧ ∀ p231x7 :
    Fin N231, ap231 h231x5 p231x7 ↔ p231x7 = p231x6) → ∀ lps231 : Fin N231 → Fin N231 → Prop, lps231 = (fun p231x8
    w231x10 : Fin N231 => ∃ h231x6 : ℕ, lpw231 h231x6 w231x10 ∧ ap231 h231x6 p231x8) → ∀ pps231 : Fin N231 → Fin
    N231 → Prop, pps231 = (fun p231x9 w231x11 : Fin N231 => ∃ h231x7 : ℕ, ppw231 h231x7 p231x9 ∧ lh231 h231x7
    w231x11) → (∃ j231x9 : ℕ, N231 + N231 + j231x9 = C231.output ∧ cone231 j231x9) ∧ (∀ (x231x4 y231x1 : Fin N231 →
    Bool) (h231x8 j231x10 : ℕ), slot231 h231x8 j231x10 → lvx231 x231x4 j231x10 → (C231.wires (List.ofFn (Fin.append
    (fun u231x2 : Fin N231 => false) y231x1))).getD h231x8 false = true → PEqualNP.MetaComplexity.circuitFun (N231 +
    N231) C231 (Fin.append x231x4 y231x1) = true) ∧ (∀ x231x5 y231x2 : Fin N231 → Bool,
    PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 y231x2) = true →
    PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 (fun u231x3 : Fin N231 => false)) =
    false → ∃ h231x9 j231x11 : ℕ, slot231 h231x9 j231x11 ∧ lvx231 x231x5 j231x11 ∧ (C231.wires (List.ofFn
    (Fin.append (fun u231x4 : Fin N231 => false) y231x2))).getD h231x9 false = true) ∧ (∀ (h231x10 j231x12 : ℕ)
    (w231x12 : Fin N231), slot231 h231x10 j231x12 → lh231 h231x10 w231x12 → ¬ lvx231 (fun a231x5 : Fin N231 =>
    decide (¬ I231 a231x5 w231x12)) j231x12) ∧ (∀ (h231x11 : ℕ) (p231x10 w231x13 : Fin N231), ap231 h231x11 p231x10
    → lh231 h231x11 w231x13 → I231 p231x10 w231x13) ∧ (∀ p231x11 w231x14 : Fin N231, I231 p231x11 w231x14 → lps231
    p231x11 w231x14 ∨ pps231 p231x11 w231x14)) → (∀ (N241 : ℕ) (I241 : Fin N241 → Fin N241 → Prop) [DecidableRel
    I241] (C241 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g241 ∈ C241.gates, (g241.op =
    PEqualNP.CircuitLowerBounds.GateOp.and ∨ g241.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g241.inputs.length =
    2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N241 + N241) C241) → (∀ j241 < C241.gates.length,
    (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i241 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241).inputs, (C241.lineDegrees (N241 + N241) (Finset.Ico N241
    (N241 + N241))).getD i241 0 = 0) ∨ (∀ h241 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241).inputs,
    (C241.lineDegrees (N241 + N241) (Finset.range N241)).getD h241 0 = 0)) → (∀ p241 p241x1 w241 w241x1 : Fin N241,
    p241 ≠ p241x1 → w241 ≠ w241x1 → I241 p241 w241 → I241 p241x1 w241 → I241 p241 w241x1 → I241 p241x1 w241x1 →
    False) → (∃ p241x2 w241x2 : Fin N241, I241 p241x2 w241x2) → (∀ p241x3 w241x3 : Fin N241, I241 p241x3 w241x3 →
    PEqualNP.MetaComplexity.circuitFun (N241 + N241) C241 (Fin.append (fun a241 : Fin N241 => decide (a241 =
    p241x3)) (fun a241x1 : Fin N241 => decide (a241x1 = w241x3))) = true) → (∀ x241 y241 : Fin N241 → Bool,
    (Finset.univ.filter (fun l241 : Fin N241 => y241 l241 = true)).card ≤ 1 → (¬ ∃ p241x4 w241x4 : Fin N241, I241
    p241x4 w241x4 ∧ x241 p241x4 = true ∧ y241 w241x4 = true) → PEqualNP.MetaComplexity.circuitFun (N241 + N241) C241
    (Fin.append x241 y241) = false) → ∀ mixed241 : ℕ → Prop, mixed241 = (fun i241x1 : ℕ => 0 < (C241.lineDegrees
    (N241 + N241) (Finset.range N241)).getD i241x1 0 ∧ 0 < (C241.lineDegrees (N241 + N241) (Finset.Ico N241 (N241 +
    N241))).getD i241x1 0) → ∀ cone241 : ℕ → Prop, cone241 = (fun j241x1 : ℕ => j241x1 < C241.gates.length ∧
    mixed241 (N241 + N241 + j241x1) ∧ Relation.ReflTransGen (fun a241x2 b241 : ℕ => a241x2 < b241 ∧ ∃ f241 : Fin
    C241.gates.length, b241 = N241 + N241 + f241.val ∧ a241x2 ∈ (C241.gates.get f241).inputs) (N241 + N241 + j241x1)
    C241.output) → ∀ gok241 : (Fin N241 → Bool) → ℕ → Prop, gok241 = (fun (x241x1 : Fin N241 → Bool) (j241x2 : ℕ) =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i241x2 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x2).inputs, (C241.lineDegrees (N241 + N241) (Finset.Ico
    N241 (N241 + N241))).getD i241x2 0 = 0 ∧ (C241.wires (List.ofFn (Fin.append x241x1 (fun u241 : Fin N241 =>
    false)))).getD i241x2 false = true) → ∀ step241 : (Fin N241 → Bool) → ℕ → ℕ → Prop, step241 = (fun (x241x2 : Fin
    N241 → Bool) (j241x3 j241x4 : ℕ) => cone241 j241x4 ∧ N241 + N241 + j241x3 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x4).inputs ∧ gok241 x241x2 j241x4) → ∀ lvx241 : (Fin N241 →
    Bool) → ℕ → Prop, lvx241 = (fun (x241x3 : Fin N241 → Bool) (j241x5 : ℕ) => cone241 j241x5 ∧ gok241 x241x3 j241x5
    ∧ ∃ j241x6 : ℕ, N241 + N241 + j241x6 = C241.output ∧ Relation.ReflTransGen (step241 x241x3) j241x5 j241x6) → ∀
    slot241 : ℕ → ℕ → Prop, slot241 = (fun h241x1 j241x7 : ℕ => cone241 j241x7 ∧ h241x1 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x7).inputs ∧ (C241.lineDegrees (N241 + N241) (Finset.range
    N241)).getD h241x1 0 = 0) → ∀ ap241 : ℕ → Fin N241 → Prop, ap241 = (fun (h241x2 : ℕ) (p241x5 : Fin N241) => ∃
    j241x8 : ℕ, slot241 h241x2 j241x8 ∧ lvx241 (fun a241x3 : Fin N241 => decide (a241x3 = p241x5)) j241x8) → ∀ lh241
    : ℕ → Fin N241 → Prop, lh241 = (fun (h241x3 : ℕ) (w241x5 : Fin N241) => (C241.wires (List.ofFn (Fin.append (fun
    u241x1 : Fin N241 => false) (fun a241x4 : Fin N241 => decide (a241x4 = w241x5))))).getD h241x3 false = true) → ∀
    lpw241 : ℕ → Fin N241 → Prop, lpw241 = (fun (h241x4 : ℕ) (w241x6 : Fin N241) => ∀ w241x7 : Fin N241, lh241
    h241x4 w241x7 ↔ w241x7 = w241x6) → ∀ lps241 : Fin N241 → Fin N241 → Prop, lps241 = (fun p241x6 w241x8 : Fin N241
    => ∃ h241x5 : ℕ, lpw241 h241x5 w241x8 ∧ ap241 h241x5 p241x6) → ∃ (TL241 TP241 : Finset (Fin N241)) (KB241 KP241
    : Finset ℕ) (own241 : ℕ → Fin N241), (∀ j241x9 ∈ KB241 ∪ KP241, cone241 j241x9 ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x9).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ Disjoint
    KB241 KP241 ∧ (∀ j241x10 ∈ KB241, ∃ p241x7 p241x8 : Fin N241, p241x7 ≠ p241x8 ∧ lvx241 (fun a241x5 : Fin N241 =>
    decide (a241x5 = p241x7)) j241x10 ∧ lvx241 (fun a241x6 : Fin N241 => decide (a241x6 = p241x8)) j241x10) ∧ (∀
    j241x11 ∈ KP241, own241 j241x11 ∈ TP241 ∧ ∀ p241x9 : Fin N241, lvx241 (fun a241x7 : Fin N241 => decide (a241x7 =
    p241x9)) j241x11 → p241x9 = own241 j241x11) ∧ (∀ p241x10 ∈ TP241, ∃ j241x12 ∈ KP241, own241 j241x12 = p241x10) ∧
    (∀ p241x11 w241x9 : Fin N241, lps241 p241x11 w241x9 → w241x9 ∈ TL241 ∨ p241x11 ∈ TP241) ∧ ∑ w241x10 : Fin N241,
    Set.ncard {p241x12 : Fin N241 | lps241 p241x12 w241x10} + TL241.card + Set.ncard {j241x13 : ℕ | cone241 j241x13}
    ≤ Set.ncard {j241x14 : ℕ | j241x14 < C241.gates.length ∧ (C241.lineDegrees (N241 + N241) (Finset.Ico N241 (N241
    + N241))).getD (N241 + N241 + j241x14) 0 = 0} + KB241.card + Set.ncard {js241 : ℕ × ℕ | cone241 js241.1 ∧
    js241.2 < 2 ∧ (C241.lineDegrees (N241 + N241) (Finset.range N241)).getD
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C241 js241.1).inputs.getD js241.2 0) 0 = 0 ∧ ∃ w241x11 : Fin N241,
    lpw241 ((PEqualNP.MetaComplexity.NestedCover.gateAt C241 js241.1).inputs.getD js241.2 0) w241x11} + Set.ncard
    {js241x1 : ℕ × ℕ | cone241 js241x1.1 ∧ js241x1.2 < 2 ∧ mixed241 ((PEqualNP.MetaComplexity.NestedCover.gateAt
    C241 js241x1.1).inputs.getD js241x1.2 0)} + 1) → (∀ (N250 k250 : ℕ) (I250 : Fin N250 → Fin N250 → Prop)
    [DecidableRel I250] (C250 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g250 ∈ C250.gates, (g250.op =
    PEqualNP.CircuitLowerBounds.GateOp.and ∨ g250.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g250.inputs.length =
    2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N250 + N250) C250) → (∀ j250 < C250.gates.length,
    (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i250 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250).inputs, (C250.lineDegrees (N250 + N250) (Finset.Ico N250
    (N250 + N250))).getD i250 0 = 0) ∨ (∀ h250 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250).inputs,
    (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD h250 0 = 0)) → (∀ p250 p250x1 w250 w250x1 : Fin N250,
    p250 ≠ p250x1 → w250 ≠ w250x1 → I250 p250 w250 → I250 p250x1 w250 → I250 p250 w250x1 → I250 p250x1 w250x1 →
    False) → (∃ p250x2 w250x2 : Fin N250, I250 p250x2 w250x2) → 1 ≤ k250 → (∀ p250x3 w250x3 : Fin N250, I250 p250x3
    w250x3 → PEqualNP.MetaComplexity.circuitFun (N250 + N250) C250 (Fin.append (fun a250 : Fin N250 => decide (a250
    = p250x3)) (fun a250x1 : Fin N250 => decide (a250x1 = w250x3))) = true) → (∀ x250 y250 : Fin N250 → Bool,
    (Finset.univ.filter (fun l250 : Fin N250 => y250 l250 = true)).card ≤ k250 → (¬ ∃ p250x4 w250x4 : Fin N250, I250
    p250x4 w250x4 ∧ x250 p250x4 = true ∧ y250 w250x4 = true) → PEqualNP.MetaComplexity.circuitFun (N250 + N250) C250
    (Fin.append x250 y250) = false) → ∀ mixed250 : ℕ → Prop, mixed250 = (fun i250x1 : ℕ => 0 < (C250.lineDegrees
    (N250 + N250) (Finset.range N250)).getD i250x1 0 ∧ 0 < (C250.lineDegrees (N250 + N250) (Finset.Ico N250 (N250 +
    N250))).getD i250x1 0) → ∀ cone250 : ℕ → Prop, cone250 = (fun j250x1 : ℕ => j250x1 < C250.gates.length ∧
    mixed250 (N250 + N250 + j250x1) ∧ Relation.ReflTransGen (fun a250x2 b250 : ℕ => a250x2 < b250 ∧ ∃ f250 : Fin
    C250.gates.length, b250 = N250 + N250 + f250.val ∧ a250x2 ∈ (C250.gates.get f250).inputs) (N250 + N250 + j250x1)
    C250.output) → ∀ gok250 : (Fin N250 → Bool) → ℕ → Prop, gok250 = (fun (x250x1 : Fin N250 → Bool) (j250x2 : ℕ) =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i250x2 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x2).inputs, (C250.lineDegrees (N250 + N250) (Finset.Ico
    N250 (N250 + N250))).getD i250x2 0 = 0 ∧ (C250.wires (List.ofFn (Fin.append x250x1 (fun u250 : Fin N250 =>
    false)))).getD i250x2 false = true) → ∀ step250 : (Fin N250 → Bool) → ℕ → ℕ → Prop, step250 = (fun (x250x2 : Fin
    N250 → Bool) (j250x3 j250x4 : ℕ) => cone250 j250x4 ∧ N250 + N250 + j250x3 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x4).inputs ∧ gok250 x250x2 j250x4) → ∀ lvx250 : (Fin N250 →
    Bool) → ℕ → Prop, lvx250 = (fun (x250x3 : Fin N250 → Bool) (j250x5 : ℕ) => cone250 j250x5 ∧ gok250 x250x3 j250x5
    ∧ ∃ j250x6 : ℕ, N250 + N250 + j250x6 = C250.output ∧ Relation.ReflTransGen (step250 x250x3) j250x5 j250x6) → ∀
    slot250 : ℕ → ℕ → Prop, slot250 = (fun h250x1 j250x7 : ℕ => cone250 j250x7 ∧ h250x1 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x7).inputs ∧ (C250.lineDegrees (N250 + N250) (Finset.range
    N250)).getD h250x1 0 = 0) → ∀ ap250 : ℕ → Fin N250 → Prop, ap250 = (fun (h250x2 : ℕ) (p250x5 : Fin N250) => ∃
    j250x8 : ℕ, slot250 h250x2 j250x8 ∧ lvx250 (fun a250x3 : Fin N250 => decide (a250x3 = p250x5)) j250x8) → ∀ lh250
    : ℕ → Fin N250 → Prop, lh250 = (fun (h250x3 : ℕ) (w250x5 : Fin N250) => (C250.wires (List.ofFn (Fin.append (fun
    u250x1 : Fin N250 => false) (fun a250x4 : Fin N250 => decide (a250x4 = w250x5))))).getD h250x3 false = true) → ∀
    lpw250 : ℕ → Fin N250 → Prop, lpw250 = (fun (h250x4 : ℕ) (w250x6 : Fin N250) => ∀ w250x7 : Fin N250, lh250
    h250x4 w250x7 ↔ w250x7 = w250x6) → ∀ ppw250 : ℕ → Fin N250 → Prop, ppw250 = (fun (h250x5 : ℕ) (p250x6 : Fin
    N250) => (∃ w250x8 w250x9 : Fin N250, w250x8 ≠ w250x9 ∧ lh250 h250x5 w250x8 ∧ lh250 h250x5 w250x9) ∧ ∀ p250x7 :
    Fin N250, ap250 h250x5 p250x7 ↔ p250x7 = p250x6) → ∀ pps250 : Fin N250 → Fin N250 → Prop, pps250 = (fun p250x8
    w250x10 : Fin N250 => ∃ h250x6 : ℕ, ppw250 h250x6 p250x8 ∧ lh250 h250x6 w250x10) → (∀ (p250x9 : Fin N250)
    (h250x7 : ℕ), ppw250 h250x7 p250x9 → ∃ j250x9 : ℕ, cone250 j250x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt
    C250 j250x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ lvx250 (fun a250x5 : Fin N250 => decide (a250x5 =
    p250x9)) j250x9 ∧ ∀ p250x10 : Fin N250, lvx250 (fun a250x6 : Fin N250 => decide (a250x6 = p250x10)) j250x9 →
    p250x10 = p250x9) ∧ ∑ p250x11 : Fin N250, min (k250 + 1) (Set.ncard {w250x11 : Fin N250 | pps250 p250x11
    w250x11}) ≤ Set.ncard {j250x10 : ℕ | j250x10 < C250.gates.length ∧ (C250.lineDegrees (N250 + N250) (Finset.range
    N250)).getD (N250 + N250 + j250x10) 0 = 0} + Set.ncard {h250x8 : ℕ | ∃ p250x12 : Fin N250, ppw250 h250x8
    p250x12} ∧ Set.ncard {js250 : ℕ × ℕ | cone250 js250.1 ∧ js250.2 < 2 ∧ (C250.lineDegrees (N250 + N250)
    (Finset.range N250)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C250 js250.1).inputs.getD js250.2 0) 0 =
    0 ∧ ∃ w250x12 : Fin N250, lpw250 ((PEqualNP.MetaComplexity.NestedCover.gateAt C250 js250.1).inputs.getD js250.2
    0) w250x12} + Set.ncard {h250x9 : ℕ | ∃ p250x13 : Fin N250, ppw250 h250x9 p250x13} ≤ Set.ncard {js250x1 : ℕ × ℕ
    | cone250 js250x1.1 ∧ js250x1.2 < 2 ∧ (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C250 js250x1.1).inputs.getD js250x1.2 0) 0 = 0}) → ∀ (N260 k260
    t260 : ℕ) (I260 : Fin N260 → Fin N260 → Prop) [DecidableRel I260] (C260 : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ p260 p260x1 w260 w260x1 : Fin N260, p260 ≠ p260x1 → w260 ≠ w260x1 → I260 p260 w260 → I260 p260x1 w260 → I260
    p260 w260x1 → I260 p260x1 w260x1 → False) → (∃ p260x2 w260x2 : Fin N260, I260 p260x2 w260x2) → 1 ≤ k260 → ((∀
    g260 ∈ C260.gates, (g260.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g260.op =
    PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g260.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack
    (N260 + N260) C260) → (∀ j260 < C260.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260).op =
    PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i260 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260
    j260).inputs, (C260.lineDegrees (N260 + N260) (Finset.Ico N260 (N260 + N260))).getD i260 0 = 0) ∨ (∀ h260 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260).inputs, (C260.lineDegrees (N260 + N260) (Finset.range
    N260)).getD h260 0 = 0)) → (∀ p260x3 w260x3 : Fin N260, I260 p260x3 w260x3 → PEqualNP.MetaComplexity.circuitFun
    (N260 + N260) C260 (Fin.append (fun a260 : Fin N260 => decide (a260 = p260x3)) (fun a260x1 : Fin N260 => decide
    (a260x1 = w260x3))) = true) → (∀ x260 y260 : Fin N260 → Bool, (Finset.univ.filter (fun l260 : Fin N260 => y260
    l260 = true)).card ≤ k260 → (¬ ∃ p260x4 w260x4 : Fin N260, I260 p260x4 w260x4 ∧ x260 p260x4 = true ∧ y260 w260x4
    = true) → PEqualNP.MetaComplexity.circuitFun (N260 + N260) C260 (Fin.append x260 y260) = false) → (∀ A260 B260 :
    Finset (Fin N260), (∀ p260x5 w260x5 : Fin N260, I260 p260x5 w260x5 → p260x5 ∈ A260 ∨ w260x5 ∈ B260) → t260 ≤
    A260.card + B260.card) → ∀ mixed260 : ℕ → Prop, mixed260 = (fun i260x1 : ℕ => 0 < (C260.lineDegrees (N260 +
    N260) (Finset.range N260)).getD i260x1 0 ∧ 0 < (C260.lineDegrees (N260 + N260) (Finset.Ico N260 (N260 +
    N260))).getD i260x1 0) → ∀ cone260 : ℕ → Prop, cone260 = (fun j260x1 : ℕ => j260x1 < C260.gates.length ∧
    mixed260 (N260 + N260 + j260x1) ∧ Relation.ReflTransGen (fun a260x2 b260 : ℕ => a260x2 < b260 ∧ ∃ f260 : Fin
    C260.gates.length, b260 = N260 + N260 + f260.val ∧ a260x2 ∈ (C260.gates.get f260).inputs) (N260 + N260 + j260x1)
    C260.output) → ∀ gok260 : (Fin N260 → Bool) → ℕ → Prop, gok260 = (fun (x260x1 : Fin N260 → Bool) (j260x2 : ℕ) =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i260x2 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x2).inputs, (C260.lineDegrees (N260 + N260) (Finset.Ico
    N260 (N260 + N260))).getD i260x2 0 = 0 ∧ (C260.wires (List.ofFn (Fin.append x260x1 (fun u260 : Fin N260 =>
    false)))).getD i260x2 false = true) → ∀ step260 : (Fin N260 → Bool) → ℕ → ℕ → Prop, step260 = (fun (x260x2 : Fin
    N260 → Bool) (j260x3 j260x4 : ℕ) => cone260 j260x4 ∧ N260 + N260 + j260x3 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x4).inputs ∧ gok260 x260x2 j260x4) → ∀ lvx260 : (Fin N260 →
    Bool) → ℕ → Prop, lvx260 = (fun (x260x3 : Fin N260 → Bool) (j260x5 : ℕ) => cone260 j260x5 ∧ gok260 x260x3 j260x5
    ∧ ∃ j260x6 : ℕ, N260 + N260 + j260x6 = C260.output ∧ Relation.ReflTransGen (step260 x260x3) j260x5 j260x6) → ∀
    slot260 : ℕ → ℕ → Prop, slot260 = (fun h260x1 j260x7 : ℕ => cone260 j260x7 ∧ h260x1 ∈
    (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x7).inputs ∧ (C260.lineDegrees (N260 + N260) (Finset.range
    N260)).getD h260x1 0 = 0) → ∀ ap260 : ℕ → Fin N260 → Prop, ap260 = (fun (h260x2 : ℕ) (p260x6 : Fin N260) => ∃
    j260x8 : ℕ, slot260 h260x2 j260x8 ∧ lvx260 (fun a260x3 : Fin N260 => decide (a260x3 = p260x6)) j260x8) → ∀ lh260
    : ℕ → Fin N260 → Prop, lh260 = (fun (h260x3 : ℕ) (w260x6 : Fin N260) => (C260.wires (List.ofFn (Fin.append (fun
    u260x1 : Fin N260 => false) (fun a260x4 : Fin N260 => decide (a260x4 = w260x6))))).getD h260x3 false = true) → ∀
    lpw260 : ℕ → Fin N260 → Prop, lpw260 = (fun (h260x4 : ℕ) (w260x7 : Fin N260) => ∀ w260x8 : Fin N260, lh260
    h260x4 w260x8 ↔ w260x8 = w260x7) → ∀ ppw260 : ℕ → Fin N260 → Prop, ppw260 = (fun (h260x5 : ℕ) (p260x7 : Fin
    N260) => (∃ w260x9 w260x10 : Fin N260, w260x9 ≠ w260x10 ∧ lh260 h260x5 w260x9 ∧ lh260 h260x5 w260x10) ∧ ∀ p260x8
    : Fin N260, ap260 h260x5 p260x8 ↔ p260x8 = p260x7) → ∀ lps260 : Fin N260 → Fin N260 → Prop, lps260 = (fun p260x9
    w260x11 : Fin N260 => ∃ h260x6 : ℕ, lpw260 h260x6 w260x11 ∧ ap260 h260x6 p260x9) → ∀ pps260 : Fin N260 → Fin
    N260 → Prop, pps260 = (fun p260x10 w260x12 : Fin N260 => ∃ h260x7 : ℕ, ppw260 h260x7 p260x10 ∧ lh260 h260x7
    w260x12) → ∑ w260x13 : Fin N260, Set.ncard {p260x11 : Fin N260 | lps260 p260x11 w260x13} + ∑ p260x12 : Fin N260,
    min (k260 + 1) (Set.ncard {w260x14 : Fin N260 | pps260 p260x12 w260x14}) + t260 ≤ C260.size + 1 := by
  intro stepCone stepEdges stepLine stepPoint N k t I decI C hC4 hEdge hk hCircuit hAnd hAccept hReject
    coverLower mixed hmixed cone hcone gok hgok step hstep lvx hlvx slot hslot ap hap
    lh hlh lpw hlpw ppw hppw lps hlps pps hpps
  classical
  have hNoLines := hReject (fun _ => true) (fun _ => false) (by simp) (by simp)
  have hRejectOne : ∀ x y : Fin N → Bool,
      (Finset.univ.filter (fun l : Fin N => y l = true)).card ≤ 1 →
      (¬ ∃ p w : Fin N, I p w ∧ x p = true ∧ y w = true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C (Fin.append x y) = false := by
    intro x y hcount hnone
    exact hReject x y (hcount.trans hk) hnone
  have hBalance := (stepCone N C hCircuit hAnd hNoLines mixed hmixed cone hcone).2.1
  have hServed := (stepEdges N I C hCircuit hAnd hC4 hEdge hAccept hRejectOne
    mixed hmixed cone hcone gok hgok step hstep lvx hlvx slot hslot ap hap
    lh hlh lpw hlpw ppw hppw lps hlps pps hpps).2.2.2.2.2
  obtain ⟨TL, TP, KB, KP, own, hGate, hDisjoint, hBoth, hOwner, hSurj, hLineCover, hLineCost⟩ :=
    stepLine N I C hCircuit hAnd hC4 hEdge hAccept hRejectOne
      mixed hmixed cone hcone gok hgok step hstep lvx hlvx slot hslot ap hap lh hlh lpw hlpw lps hlps
  obtain ⟨hSingle, hPointCost, hSlotCost⟩ :=
    stepPoint N k I C hCircuit hAnd hC4 hEdge hk hAccept hReject
      mixed hmixed cone hcone gok hgok step hstep lvx hlvx slot hslot ap hap lh hlh lpw hlpw ppw hppw pps hpps

  let allGates : Set ℕ := ↑(Finset.range C.gates.length)
  let noLine : Set ℕ := {j | j < C.gates.length ∧
    (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (N + N + j) 0 = 0}
  let noPoint : Set ℕ := {j | j < C.gates.length ∧
    (C.lineDegrees (N + N) (Finset.range N)).getD (N + N + j) 0 = 0}
  have hConeData (j : ℕ) (hj : cone j) : j < C.gates.length ∧
      0 < (C.lineDegrees (N + N) (Finset.range N)).getD (N + N + j) 0 ∧
      0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (N + N + j) 0 := by
    rw [hcone] at hj
    exact ⟨hj.1, by simpa only [hmixed] using hj.2.1⟩
  have hAll : allGates.Finite := (Finset.range C.gates.length).finite_toSet
  have hConeSub : {j | cone j} ⊆ allGates := by
    intro j hj
    exact Finset.mem_range.mpr (hConeData j hj).1
  have hConeFinite : {j | cone j}.Finite := hAll.subset hConeSub
  have hNoLineSub : noLine ⊆ allGates := by
    intro j hj
    exact Finset.mem_range.mpr hj.1
  have hNoPointSub : noPoint ⊆ allGates := by
    intro j hj
    exact Finset.mem_range.mpr hj.1
  have hPureDisjoint : Disjoint noLine noPoint := by
    refine Set.disjoint_left.mpr ?_
    intro j hj hq
    have hWire := wireDegree_pos N C (fun g hg => (hCircuit.1 g hg).2) hCircuit.2
      (Nat.add_lt_add_left hj.1 (N + N))
    exact hWire.elim (fun hp => (Nat.ne_of_gt hp) hq.2) (fun hl => (Nat.ne_of_gt hl) hj.2)
  have hNoLineCone : Disjoint noLine {j | cone j} := by
    refine Set.disjoint_left.mpr ?_
    intro j hj hc
    exact (Nat.ne_of_gt (hConeData j hc).2.2) hj.2
  have hNoPointCone : Disjoint noPoint {j | cone j} := by
    refine Set.disjoint_left.mpr ?_
    intro j hj hc
    exact (Nat.ne_of_gt (hConeData j hc).2.1) hj.2
  have hTotal : noLine.ncard + noPoint.ncard + Set.ncard {j | cone j} ≤ C.size := by
    have h := threeCards hAll hNoLineSub hNoPointSub hConeSub hPureDisjoint hNoLineCone hNoPointCone
    simpa [allGates, Circuit.size] using h

  let A : Finset (Fin N) := TP ∪ Finset.univ.filter (fun p => ∃ w, pps p w)
  have hCover : t ≤ A.card + TL.card := by
    refine coverLower A TL ?_
    intro p w he
    rcases hServed p w he with hl | hp
    · rcases hLineCover p w hl with hw | hpt
      · exact Or.inr hw
      · exact Or.inl (Finset.mem_union_left _ hpt)
    · exact Or.inl (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ p, w, hp⟩))

  let live (p : Fin N) (j : ℕ) : Prop := lvx (fun a => decide (a = p)) j
  let available : Set ℕ := {j | cone j ∧ (gateAt C j).op = GateOp.and ∧ j ∉ KB}
  let orCone : Set ℕ := {j | cone j ∧ (gateAt C j).op = GateOp.or}
  let assigned (j : ℕ) (p : Fin N) : Prop :=
    (j ∈ KP ∧ own j = p) ∨ (j ∉ KP ∧ live p j ∧ ∀ q, live q j → q = p)
  have hChoose : ∀ p ∈ A, ∃ j ∈ available, assigned j p := by
    intro p hp
    by_cases htp : p ∈ TP
    · obtain ⟨j, hj, he⟩ := hSurj p htp
      have hgate := hGate j (Finset.mem_union_right KB hj)
      have hnot : j ∉ KB := fun hb => Finset.disjoint_left.mp hDisjoint hb hj
      exact ⟨j, ⟨hgate.1, hgate.2, hnot⟩, Or.inl ⟨hj, he⟩⟩
    · have hpw := (Finset.mem_union.mp hp).resolve_left htp
      obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hpw).2
      have witness : ∃ h : ℕ, ppw h p ∧ lh h w := by simpa only [hpps] using hw
      obtain ⟨h, hh, _⟩ := witness
      obtain ⟨j, hc, hj, hpj, huniq⟩ := hSingle p h hh
      have hnotB : j ∉ KB := by
        intro hb
        obtain ⟨p₁, p₂, hne, h₁, h₂⟩ := hBoth j hb
        exact hne ((huniq p₁ h₁).trans (huniq p₂ h₂).symm)
      have hnotP : j ∉ KP := by
        intro hkp
        have he := (hOwner j hkp).2 p hpj
        exact htp (he.symm ▸ (hOwner j hkp).1)
      exact ⟨j, ⟨hc, hj, hnotB⟩, Or.inr ⟨hnotP, hpj, huniq⟩⟩
  have hUnique (j : ℕ) (p q : Fin N) (hp : assigned j p) (hq : assigned j q) : p = q := by
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact hp.2.symm.trans hq.2
    · exact (hq.1 hp.1).elim
    · exact (hp.1 hq.1).elim
    · exact (hp.2.2 q hq.2.1).symm
  choose f hf using hChoose
  let pick (p : Fin N) : ℕ := if hp : p ∈ A then f p hp else 0
  have hPick (p : Fin N) (hp : p ∈ A) : pick p ∈ available ∧ assigned (pick p) p := by
    simpa [pick, hp] using hf p hp
  have hAvailSub : available ⊆ {j | cone j} := fun _ h => h.1
  have hACard : A.card ≤ available.ncard := by
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn pick (fun p hp => (hPick p hp).1) ?_
      (hConeFinite.subset hAvailSub)
    intro p hp q hq hpq
    exact hUnique (pick p) p q (hPick p hp).2 (hpq.symm ▸ (hPick q hq).2)
  have hKBSub : (↑KB : Set ℕ) ⊆ {j | cone j} := by
    intro j hj
    exact (hGate j (Finset.mem_union_left KP hj)).1
  have hOrSub : orCone ⊆ {j | cone j} := fun _ hj => hj.1
  have hAvailKB : Disjoint available (↑KB : Set ℕ) :=
    Set.disjoint_left.mpr (fun _ ha hb => ha.2.2 hb)
  have hAvailOr : Disjoint available orCone := by
    refine Set.disjoint_left.mpr ?_
    intro j ha ho
    exact GateOp.noConfusion (ha.2.1.symm.trans ho.2)
  have hKBOr : Disjoint (↑KB : Set ℕ) orCone := by
    refine Set.disjoint_left.mpr ?_
    intro j hb ho
    exact GateOp.noConfusion ((hGate j (Finset.mem_union_left KP hb)).2.symm.trans ho.2)
  have hMixedBudget : A.card + KB.card + orCone.ncard ≤ Set.ncard {j | cone j} := by
    have h := threeCards hConeFinite hAvailSub hKBSub hOrSub hAvailKB hAvailOr hKBOr
    simp only [Set.ncard_coe_finset] at h
    omega

  let lineSlots : Set (ℕ × ℕ) := {js | cone js.1 ∧ js.2 < 2 ∧
    (C.lineDegrees (N + N) (Finset.range N)).getD ((gateAt C js.1).inputs.getD js.2 0) 0 = 0 ∧
    ∃ w : Fin N, lpw ((gateAt C js.1).inputs.getD js.2 0) w}
  let pureSlots : Set (ℕ × ℕ) := {js | cone js.1 ∧ js.2 < 2 ∧
    (C.lineDegrees (N + N) (Finset.range N)).getD ((gateAt C js.1).inputs.getD js.2 0) 0 = 0}
  let mixedSlots : Set (ℕ × ℕ) := {js | cone js.1 ∧ js.2 < 2 ∧
    mixed ((gateAt C js.1).inputs.getD js.2 0)}
  let witnesses : Set ℕ := {h | ∃ p : Fin N, ppw h p}
  change orCone.ncard + Set.ncard {j | cone j} = pureSlots.ncard + mixedSlots.ncard at hBalance
  change (∑ w : Fin N, Set.ncard {p : Fin N | lps p w}) + TL.card + Set.ncard {j | cone j} ≤
    noLine.ncard + KB.card + lineSlots.ncard + mixedSlots.ncard + 1 at hLineCost
  change (∑ p : Fin N, min (k + 1) (Set.ncard {w : Fin N | pps p w})) ≤
    noPoint.ncard + witnesses.ncard at hPointCost
  change lineSlots.ncard + witnesses.ncard ≤ pureSlots.ncard at hSlotCost
  omega
