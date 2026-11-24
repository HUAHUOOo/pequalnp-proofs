import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2596_aux
def valid (g : Gate) := g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
  g.inputs.length ≤ 2
def flat (c : Bool) : Gate := if c then ⟨.and,[]⟩ else ⟨.or,[]⟩
def fixPin (n : ℕ) (c : Bool) (g : Gate) : Gate :=
  match g.op with
  | .and => if !c && g.inputs.contains n then flat false else ⟨.and,g.inputs.filter (· != n)⟩
  | .or => if c && g.inputs.contains n then flat true else ⟨.or,g.inputs.filter (· != n)⟩
  | .not => if g.inputs.head?=some n then flat (!c) else g
  | _ => g
def rename (n r : ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map fun i => if i=n then r else i⟩
def convert (n r : ℕ) (f : Bool → Bool) (g : Gate) : Gate :=
  match f false,f true with
  | false,true => rename n r g
  | true,false => g
  | false,false => fixPin n false g
  | true,true => fixPin n true g
def ev (g : Gate) (wire : ℕ → Bool) := g.op.eval (g.inputs.map wire)
def step (v : List Bool) (g : Gate) := v++[ev g (fun i => v.getD i false)]
lemma validFix (n : ℕ) (c : Bool) (g : Gate) (h : valid g) : valid (fixPin n c g) := by
  obtain ⟨basis, size⟩ := h
  rcases basis with d|d|d <;> cases g with
  | mk op pins =>
    simp only at d
    subst op
    cases c <;> simp only [fixPin] <;> split <;>
      simp_all [valid,flat] <;> exact (List.length_filter_le ..).trans size
lemma validConvert (n r : ℕ) (f : Bool → Bool) (g : Gate) (h : valid g) :
    valid (convert n r f g) := by
  unfold convert
  split
  · simpa [rename,valid] using h
  · exact h
  · exact validFix _ _ _ h
  · exact validFix _ _ _ h
lemma fixValue {g : Gate} (hg : valid g) (n : ℕ) (c : Bool) (w v : ℕ → Bool)
    (atPin : w n = c) (rest : ∀ i, i≠n → w i = v i) :
    ev g w = ev (fixPin n c g) v := by
  have rev (i : ℕ) : (n=i) ↔ (i=n) := eq_comm
  have eq (i) : w i = (if i=n then c else v i) := by
    by_cases h : i=n <;> simp_all
  obtain ⟨basis,hl⟩ := hg
  obtain ⟨op,pins⟩ := g
  change op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) at basis
  change pins.length≤2 at hl
  rcases basis with rfl|rfl|rfl <;> cases pins with
  | nil => cases c <;> simp [fixPin,flat,ev,GateOp.eval]
  | cons a pins =>
    cases pins with
    | nil => by_cases ha : a=n <;> cases c <;> simp_all [fixPin,flat,ev,GateOp.eval,eq,rev]
    | cons b pins =>
      cases pins with
      | nil =>
        by_cases ha : a=n <;> by_cases hb : b=n <;> cases c <;>
          simp_all [fixPin,flat,ev,GateOp.eval,eq,rev]
      | cons d ds => simp at hl
def state {n : ℕ} (x : Fin n → Bool) (c : Bool) (acc : List Bool) := List.ofFn x ++ c::acc
lemma pin {n : ℕ} (x : Fin n → Bool) (c : Bool) (acc : List Bool) :
    (state x c acc).getD n false=c := by
  simp [state,List.getD_eq_getElem?_getD,List.getElem?_append_right]
lemma raw {n : ℕ} (x : Fin n → Bool) (c : Bool) (acc : List Bool) (r : Fin n) :
    (state x c acc).getD r.val false=x r := by
  unfold state
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_left (show r.val < (List.ofFn x).length by simpa using r.isLt)]
  simp
lemma other {n : ℕ} (x : Fin n → Bool) (c d : Bool) (acc : List Bool) (i : ℕ) (hi : i ≠ n) :
    (state x c acc).getD i false=(state x d acc).getD i false := by
  by_cases small : i<n
  · rw [raw (r:=⟨i,small⟩),raw (r:=⟨i,small⟩)]
  · obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show n+1 ≤ i by omega)
    subst i
    simp [state,List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp;omega :
      (List.ofFn x).length ≤ n+1+j),show n+1+j-n=j+1 by omega]
lemma same {n : ℕ} (r : Fin n) (f : Bool → Bool) (g : Gate) (hg : valid g)
    (x : Fin n → Bool) (acc : List Bool) :
    ev g (fun i => (state x (f (x r)) acc).getD i false) =
    ev (convert n r.val f g) (fun i => (state x (!(x r)) acc).getD i false) := by
  generalize h0 : f false = ff
  generalize h1 : f true = tt
  cases ff <;> cases tt
  · simp only [convert,h0,h1]
    apply fixValue hg
    · rw [pin]; cases h : x r <;> simp_all
    · exact other _ _ _ _
  · simp only [convert,h0,h1,rename,ev,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro i _
    by_cases he : i=n
    · subst i; simp only [ite_true,pin,raw]; cases h : x r <;> simp_all
    · simp only [ite_eq_right he]
      exact other _ _ _ _ _ he
  · have h : f (x r) = !(x r) := by cases hx : x r <;> simp_all
    simp [convert,h0,h1,h]
  · simp only [convert,h0,h1]
    apply fixValue hg
    · rw [pin]; cases h : x r <;> simp_all
    · exact other _ _ _ _
lemma run {n : ℕ} (r : Fin n) (f : Bool → Bool) (gs : List Gate)
    (basis : ∀g∈gs, valid g) (x : Fin n → Bool) (acc : List Bool) :
    ∃ v : List Bool,
      gs.foldl step (state x (f (x r)) acc) = state x (f (x r)) v ∧
      (gs.map (convert n r.val f)).foldl step (state x (!(x r)) acc) = state x (!(x r)) v := by
  induction gs generalizing acc with
  | nil => exact ⟨acc,rfl,rfl⟩
  | cons g gs ih =>
    let z := ev g (fun i => (state x (f (x r)) acc).getD i false)
    have e := same r f g (basis g (by simp)) x acc
    obtain ⟨v,ho,hn⟩ := ih (fun q hq => basis q (by simp [hq])) (acc++[z])
    refine ⟨v,?_,?_⟩
    · simpa only [List.foldl_cons,step,state,List.append_assoc,List.cons_append,z] using ho
    · simp only [List.map_cons,List.foldl_cons,step]
      rw [←e]
      simpa only [state,z,List.append_assoc,List.cons_append] using hn

theorem simulate (n : ℕ) (r : Fin n) (f : Bool → Bool) (C : Circuit)
    (basis : FanInTwo C) (hout : C.output ≠ n) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧ ∀ x : Fin n → Bool,
      D.eval (List.ofFn x ++ [!(x r)]) = C.eval (List.ofFn x ++ [f (x r)]) := by
  let D : Circuit := ⟨C.gates.map (convert n r.val f),C.output⟩
  refine ⟨D,?_,by simp [D,Circuit.size],?_⟩
  · intro g hg
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    exact validConvert _ _ _ _ (basis q hq)
  · intro x
    obtain ⟨v,ho,hn⟩ := run r f C.gates basis x []
    change ((C.gates.map _).foldl step (state x (!(x r)) [])).getD C.output false =
      (C.gates.foldl step (state x (f (x r)) [])).getD C.output false
    rw [ho,hn]
    exact other _ _ _ _ _ hout
end PEqualNP.Outside.L_meta_2596_aux

theorem PEqualNP.Outside.L_meta_2596 : ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : Bool → Bool) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.output ≠ x1 → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size ≤ x4.size ∧ ∀ (x8 : Fin x1 → Bool), x7.eval (List.ofFn x8 ++ [!x8 x2]) = x4.eval (List.ofFn x8 ++ [x3 (x8 x2)]) :=
  PEqualNP.Outside.L_meta_2596_aux.simulate
