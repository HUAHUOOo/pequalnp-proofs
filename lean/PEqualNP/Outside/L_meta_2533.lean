import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2533_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def move (k p i : ℕ) := if i=k then p else if i<k then i else i-1
def adjust (k p : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (move k p)⟩
def step (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
def valid (g : Gate) := g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2
lemma valid_adj (k p : ℕ) (g : Gate) (hg : valid g) : valid (adjust k p g) := by
  simpa [valid,adjust] using hg
lemma splice (base acc : List Bool) (v : Bool) (p i : ℕ)
    (hval : (base++acc).getD p false=v) :
    (base ++ v::acc).getD i false = (base++acc).getD (move base.length p i) false := by
  by_cases he : i=base.length
  · subst i
    simp [move,List.getD_eq_getElem?_getD,List.getElem?_append_right,←hval]
  · by_cases hl : i<base.length
    · simp [move,he,hl,List.getD_eq_getElem?_getD,List.getElem?_append_left hl]
    · obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show base.length+1 ≤ i by omega)
      subst i
      simp only [move,ite_eq_right he,ite_eq_right hl,List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega),List.getElem?_append_right (by omega)]
      simp [show base.length+1+j-base.length=j+1 by omega,
        show base.length+1+j-1-base.length=j by omega]

lemma tailSim (gs : List Gate) (base : List Bool) (v : Bool) (p limit : ℕ)
    (hval : ∀ acc : List Bool, acc.length ≤ limit → (base++acc).getD p false=v)
    (acc : List Bool) (bound : acc.length+gs.length ≤ limit) :
    ∃ out : List Bool, out.length=acc.length+gs.length ∧
      gs.foldl step (base++v::acc) = base++v::out ∧
      (gs.map (adjust base.length p)).foldl step (base++acc) = base++out := by
  induction gs generalizing acc with
  | nil => exact ⟨acc,by simp,rfl,rfl⟩
  | cons g gs ih =>
    let z := g.op.eval (g.inputs.map fun i => (base++v::acc).getD i false)
    have l : acc.length+1+gs.length ≤ limit := by simp at bound; omega
    have same : (adjust base.length p g).op.eval ((adjust base.length p g).inputs.map
        fun i => (base++acc).getD i false) = z := by
      simp only [adjust,List.map_map,Function.comp_def,z]
      congr 1
      apply List.map_congr_left
      intro i _
      exact (splice base acc v p i (hval acc (by omega))).symm
    obtain ⟨out,h1,h2,h3⟩ := ih (acc++[z]) (by simpa using l)
    refine ⟨out,by simp at h1 ⊢; omega,?_,?_⟩
    · simpa only [List.foldl_cons,step,List.append_assoc,List.cons_append,z] using h2
    · simp only [List.map_cons,List.foldl_cons,step,same,List.append_assoc]
      exact h3

lemma simulate (gs : List Gate) (base : List Bool) (v : Bool) (p o : ℕ)
    (hval : ∀ acc : List Bool, acc.length≤gs.length → (base++acc).getD p false=v) :
    ((gs.map (adjust base.length p)).foldl step base).getD (move base.length p o) false =
      (gs.foldl step (base++[v])).getD o false := by
  obtain ⟨out,hl,ho,hn⟩ := tailSim gs base v p gs.length hval [] (by simp)
  simp only [List.length_nil,Nat.zero_add,List.append_nil] at hl ho hn
  rw [ho,hn]
  exact (splice base out v p o (hval _ hl.le)).symm

lemma stable (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i<w.length) :
    (gs.foldl step w).getD i false=w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih (step w g) (by simp [step];omega)]
    simp [step,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
lemma length_run (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons,ih,step]; omega

def pick (n : ℕ) (pins : List ℕ) : ℕ := (pins.erase n).headD n
lemma orFalse (pins : List ℕ) (n : ℕ) (hn : n∈pins) (hl : pins.length≤2)
    (w : List Bool) (hz : w.getD n false=false) :
    GateOp.or.eval (pins.map fun i => w.getD i false) = w.getD (pick n pins) false := by
  cases pins with
  | nil => simp at hn
  | cons a pins =>
    cases pins with
    | nil => simp at hn; subst a; simp [pick,GateOp.eval]
    | cons b pins =>
      cases pins with
      | nil =>
        rcases List.mem_cons.mp hn with h|h
        · subst a; simp [pick,GateOp.eval,List.getD_eq_getElem?_getD] at *
          simp_all
        · have h': n=b := by simpa using h
          subst b
          by_cases he : a=n <;> simp_all [pick,GateOp.eval,List.getD_eq_getElem?_getD]
      | cons c cs => simp at hl

def hide (n : ℕ) (D : Circuit) : Circuit :=
  ⟨D.gates.map (adjust n (n+D.size)),move n (n+D.size) D.output⟩
lemma hide_eval (n : ℕ) (D : Circuit) (x : Fin n → Bool) :
    (hide n D).eval (List.ofFn x) = D.eval (List.ofFn x++[false]) := by
  have h := simulate D.gates (List.ofFn x) false (n+D.size) D.output (by
    intro acc ha
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp [Circuit.size];omega)]
    rfl)
  change ((D.gates.map (adjust n (n+D.size))).foldl step (List.ofFn x)).getD
    (move n (n+D.size) D.output) false = (D.gates.foldl step (List.ofFn x++[false])).getD D.output false
  simpa only [List.length_ofFn] using h

theorem remove_or (n : ℕ) (pre post : List Gate) (pins : List ℕ) (o : ℕ) (hn : n∈pins) :
    let C : Circuit := ⟨pre++⟨.or,pins⟩::post,o⟩
    FanInTwo C → HasCircuitSize n (fun x => C.eval (List.ofFn x++[false])) (pre.length+post.length) := by
  dsimp only
  intro fan
  let k := n+1+pre.length
  let p := if pick n pins < k then pick n pins else n
  let D : Circuit := ⟨pre++post.map (adjust k p),move k p o⟩
  have fD : FanInTwo D := by
    intro g hg
    rcases List.mem_append.mp hg with h|h
    · exact fan g (by simp [h])
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
      exact valid_adj _ _ _ (fan q (by simp [hq]))
  refine ⟨hide n D,?_,by simp [hide,D,Circuit.size],?_⟩
  · intro g hg
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    exact valid_adj _ _ _ (fD q hq)
  · intro x
    rw [hide_eval]
    let w := pre.foldl step (List.ofFn x++[false])
    have lw : w.length=k := by simp [w,length_run,k]
    have nz : w.getD n false=false := by
      rw [show w.getD n false=(List.ofFn x++[false]).getD n false from stable _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_right]
    have pn : p<w.length := by dsimp [p];split <;> simp_all [k] <;> omega
    have plen : pins.length ≤ 2 := (fan ⟨.or,pins⟩ (by simp)).2
    have same : step w ⟨.or,pins⟩ = w++[w.getD p false] := by
      simp only [step,orFalse pins n hn plen w nz]
      unfold p
      split
      · rfl
      · rename_i h
        simp only [List.getD_eq_getElem?_getD] at nz ⊢
        rw [List.getElem?_eq_none (show w.length ≤ pick n pins by omega)]
        simp_all
    have sim := simulate post w (w.getD p false) p o (by
      intro acc _
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left pn])
    rw [lw] at sim
    change ((pre++post.map (adjust k p)).foldl step (List.ofFn x++[false])).getD (move k p o) false =
      ((pre++⟨.or,pins⟩::post).foldl step (List.ofFn x++[false])).getD o false
    simp only [List.foldl_append,List.foldl_cons]
    change _ = (post.foldl step (step w ⟨.or,pins⟩)).getD o false
    rw [same]
    exact sim
end PEqualNP.Outside.L_meta_2533_aux
theorem PEqualNP.Outside.L_meta_2533 : ∀ (x1 : ℕ) (x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : List ℕ) (x5 : ℕ),   x1 ∈ x4 →     have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x4 : PEqualNP.CircuitLowerBounds.Gate } :: x3, output := x5 : PEqualNP.CircuitLowerBounds.Circuit };     PEqualNP.MetaComplexity.FanInTwo x7 → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x9 : Fin x1 → Bool) => x7.eval (List.ofFn x9 ++ [Bool.false])) (x2.length + x3.length) :=
  PEqualNP.Outside.L_meta_2533_aux.remove_or
