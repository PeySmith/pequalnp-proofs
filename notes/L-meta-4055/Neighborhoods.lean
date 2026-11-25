import PEqualNP.Defs

-- Kurt Mehlhorn, Some Remarks on Boolean Sums, Acta Informatica 12 (1979), 371–375,
-- gives general lower bounds for monotone networks computing disjoint families of Boolean sums.
-- This proof counts paid binary ORs in the cyclic plane on the singleton and all-nonneighbor tests.
-- A charged gate accepts two distinct line singletons. The intersection of two neighborhoods
-- has at most one line, so a charged gate can contribute to at most one output.

namespace PEqualNP.Outside.PlaneNeighborhood

abbrev V := Fin 21
abbrev Input := V → Bool
abbrev Wire := Input → Bool
abbrev Row := Finset ℕ × Finset ℕ

def N (p : V) : Finset V := Finset.univ.filter (fun l =>
  ([(p.val+20)%21, p.val, (p.val+5)%21, (p.val+7)%21, (p.val+17)%21] : List ℕ).contains l.val)
def one (l : V) : Input := fun j => decide (j = l)
def outsideN (p : V) : Input := fun l => decide (l ∉ N p)
def zeroWire : Wire := fun _ => false
def inputWires : List Wire := List.ofFn (fun j : V => fun x : Input => x j) ++ [zeroWire]
def conjunction (w : List Wire) (s : Finset ℕ) : Wire :=
  fun x => decide (∀ i ∈ s, (w.getD i zeroWire) x = true)
def gate (w : List Wire) (r : Row) : Wire := fun x => conjunction w r.1 x || conjunction w r.2 x
def history (R : List Row) : List Wire :=
  R.foldl (fun acc r => acc ++ [gate (inputWires ++ acc) r]) []
def wires (R : List Row) := inputWires ++ history R
theorem history_snoc (R : List Row) (r : Row) : history (R ++ [r]) = history R ++ [gate (wires R) r] := by
  simp [history, wires, List.foldl_append]
theorem wires_snoc (R : List Row) (r : Row) : wires (R ++ [r]) = wires R ++ [gate (wires R) r] := by
  simp [wires, history_snoc]
theorem history_length (R : List Row) : (history R).length = R.length := by
  induction R using List.reverseRecOn with
  | nil => rfl
  | append_singleton R r ih => simp [history_snoc, ih]

def Safe (f : Wire) : Prop := ∀ p l, l ∉ N p → f (one l) = true → f (outsideN p) = true
def MonoColor (p : V) (c : V → V) (f : Wire) : Prop :=
  f (outsideN p) = false → ∀ i j, f (one i) = true → f (one j) = true → c i = c j
def Charged (p : V) (f : Wire) : Prop :=
  f (outsideN p) = false ∧ ∃ i j : V, i ≠ j ∧ f (one i) = true ∧ f (one j) = true
noncomputable def charges (p : V) (fs : List Wire) : ℕ := by
  classical exact (fs.filter fun f => decide (Charged p f)).length

theorem getD_prop {P : Wire → Prop} {ws : List Wire}
    (all : ∀ f ∈ ws, P f) (zero : P zeroWire) (i : ℕ) : P (ws.getD i zeroWire) := by
  by_cases h : i < ws.length
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h] using all ws[i] (List.getElem_mem h)
  · simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt h)] using zero
theorem safe_zero : Safe zeroWire := by simp [Safe,zeroWire]
theorem mono_zero (p : V) (c : V → V) : MonoColor p c zeroWire := by simp [MonoColor,zeroWire]
theorem safe_inputs : ∀ f ∈ inputWires, Safe f := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · obtain ⟨j,hj⟩ := List.mem_ofFn.mp hf
    subst f
    intro p l hn hit
    have hjl : j = l := by simpa [one] using hit
    simpa [outsideN,hjl] using hn
  · have eq := List.mem_singleton.mp hf
    subst f; exact safe_zero
theorem mono_inputs (p : V) : ∀ f ∈ inputWires, MonoColor p id f := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · obtain ⟨v,hv⟩ := List.mem_ofFn.mp hf
    subst f
    intro d i j hi hj
    have hvi : v = i := by simpa [one] using hi
    have hvj : v = j := by simpa [one] using hj
    exact hvi.symm.trans hvj
  · have eq := List.mem_singleton.mp hf
    subst f
    exact mono_zero p _
theorem safe_and {ws : List Wire} (all : ∀ f ∈ ws, Safe f) (s : Finset ℕ) : Safe (conjunction ws s) := by
  intro p l hn hit
  apply decide_eq_true
  intro i hi
  exact getD_prop all safe_zero i p l hn ((of_decide_eq_true hit) i hi)
theorem safe_gate {ws : List Wire} (all : ∀ f ∈ ws, Safe f) (r : Row) : Safe (gate ws r) := by
  intro p l hn hit
  rcases Bool.or_eq_true_iff.mp hit with a|b
  · exact Bool.or_eq_true_iff.mpr (.inl (safe_and all r.1 p l hn a))
  · exact Bool.or_eq_true_iff.mpr (.inr (safe_and all r.2 p l hn b))
theorem safe_wires (R : List Row) : ∀ f ∈ wires R, Safe f := by
  induction R using List.reverseRecOn with
  | nil => simpa [wires,history] using safe_inputs
  | append_singleton R r ih =>
    rw [wires_snoc]
    intro f hf
    rcases List.mem_append.mp hf with a|b
    · exact ih f a
    · have eq := List.mem_singleton.mp b
      subst f; exact safe_gate ih r

theorem mono_and {cs : V → V} {p : V} {ws : List Wire} (all : ∀ f ∈ ws, MonoColor p cs f)
    (s : Finset ℕ) : MonoColor p cs (conjunction ws s) := by
  classical
  intro off i j hi hj
  have no : ¬ ∀ n ∈ s, (ws.getD n zeroWire) (outsideN p) = true :=
    of_decide_eq_false off
  push Not at no
  obtain ⟨n,hn,bad⟩ := no
  have unlit : (ws.getD n zeroWire) (outsideN p) = false := by simpa using bad
  exact getD_prop all (mono_zero p cs) n unlit i j
    ((of_decide_eq_true hi) n hn) ((of_decide_eq_true hj) n hn)

theorem one_color {p : V} {c : V → V} {f : Wire} (m : MonoColor p c f) (off : f (outsideN p) = false) :
    ∃ a : V, ∀ i, f (one i) = true → c i = a := by
  by_cases h : ∃ i, f (one i) = true
  · obtain ⟨i,hi⟩ := h
    exact ⟨c i,fun j hj => m off j i hj hi⟩
  · exact ⟨0, fun i hi => (h ⟨i,hi⟩).elim⟩

def identify (a b z : V) : V := if z=b then a else z
theorem image_loss (T : Finset V) (a b : V) : T.card ≤ (T.image (identify a b)).card + 1 := by
  have sub : T ⊆ insert b (T.image (identify a b)) := by
    intro x hx
    by_cases eq : x = b
    · simp [eq]
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x,hx,by simp [identify,eq]⟩)
  exact (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)

theorem recolor {p : V} {c : V → V} {ws : List Wire} (all : ∀ f ∈ ws, MonoColor p c f)
    (r : Row) (ch : Charged p (gate ws r)) :
    ∃ c' : V → V, ((N p).image c).card ≤ ((N p).image c').card + 1 ∧
       ∀ f ∈ ws ++ [gate ws r], MonoColor p c' f := by
  have off := Bool.or_eq_false_iff.mp ch.1
  obtain ⟨a,ha⟩ := one_color (mono_and all r.1) off.1
  obtain ⟨b,hb⟩ := one_color (mono_and all r.2) off.2
  let c' := identify a b ∘ c
  refine ⟨c', ?_, ?_⟩
  · simpa only [c',Finset.image_image,Function.comp_def] using image_loss ((N p).image c) a b
  · intro f hf
    rcases List.mem_append.mp hf with hf|hf
    · intro d i j hi hj
      exact congrArg (identify a b) (all f hf d i j hi hj)
    · have eq := List.mem_singleton.mp hf
      subst f
      have colored (i : V) (hi : gate ws r (one i) = true) : c' i = a := by
        rcases Bool.or_eq_true_iff.mp hi with u|v
        · simp [c',Function.comp_def,ha i u,identify]
        · simp [c',Function.comp_def,hb i v,identify]
      exact fun _ i j hi hj => (colored i hi).trans (colored j hj).symm
theorem uncharged {p : V} {c : V → V} {f : Wire} (h : ¬ Charged p f) : MonoColor p c f := by
  intro off i j hi hj
  by_cases e : i=j
  · simp [e]
  · exact (h ⟨off,i,j,e,hi,hj⟩).elim
theorem colors (p : V) (R : List Row) :
    ∃ c : V → V, (N p).card ≤ ((N p).image c).card + charges p (history R) ∧
      ∀ f ∈ wires R, MonoColor p c f := by
  classical
  induction R using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, ?_⟩
    · simp [history,charges]
    · simpa [wires,history] using mono_inputs p
  | append_singleton R r ih =>
    obtain ⟨c,ct,all⟩ := ih
    rw [history_snoc,wires_snoc]
    by_cases hit : Charged p (gate (wires R) r)
    · obtain ⟨c',le,news⟩ := recolor all r hit
      refine ⟨c',?_,news⟩
      have inc : charges p (history R ++ [gate (wires R) r]) = charges p (history R) + 1 := by
        simp [charges,hit]
      omega
    · refine ⟨c,?_,?_⟩
      · simpa [charges,hit] using ct
      · intro f hf
        rcases List.mem_append.mp hf with hf|hf
        · exact all f hf
        · have eq := List.mem_singleton.mp hf
          subst f; exact uncharged hit

theorem neighborhood_size : ∀ p : V, (N p).card = 5 := by decide +kernel
set_option maxHeartbeats 1000000 in
theorem codegree : ∀ p q : V, p ≠ q → (N p ∩ N q).card ≤ 1 := by decide +kernel

theorem charged_unique {f : Wire} (sf : Safe f) {p q : V} (hp : Charged p f) (hq : Charged q f) : p = q := by
  by_contra ne
  obtain ⟨i,j,ij,hi,hj⟩ := hp.2
  have member {r l : V} (off : f (outsideN r) = false) (hit : f (one l) = true) : l ∈ N r := by
    by_contra h
    exact Bool.false_ne_true (off.symm.trans (sf r l h hit))
  have sub : ({i,j} : Finset V) ⊆ N p ∩ N q := by
    intro l hl
    rcases Finset.mem_insert.mp hl with rfl|hl
    · exact Finset.mem_inter.mpr ⟨member hp.1 hi,member hq.1 hi⟩
    · obtain rfl := Finset.mem_singleton.mp hl
      exact Finset.mem_inter.mpr ⟨member hp.1 hj,member hq.1 hj⟩
  have lim := (Finset.card_le_card sub).trans (codegree p q ne)
  simp [ij] at lim

theorem charge_one {f : Wire} (sf : Safe f) :
    (∑ p : V, (@ite ℕ (Charged p f) (Classical.propDecidable _) 1 0)) ≤ 1 := by
  classical
  by_cases h : ∃ p, Charged p f
  · obtain ⟨p,hp⟩ := h
    have hh (q : V) : Charged q f ↔ q=p := ⟨fun hq => charged_unique sf hq hp,fun eq => eq.symm ▸ hp⟩
    simp [hh]
  · have hn (p : V) : ¬ Charged p f := fun hp => h ⟨p,hp⟩
    simp [hn]

theorem total_charges (fs : List Wire) (all : ∀ f ∈ fs, Safe f) :
    (∑ p : V, charges p fs) ≤ fs.length := by
  classical
  induction fs with
  | nil => simp [charges]
  | cons f fs ih =>
    have tail := ih (fun z hz => all z (List.mem_cons_of_mem _ hz))
    have head := charge_one (all f (by simp))
    have split (p : V) : charges p (f::fs) = charges p fs + (if Charged p f then 1 else 0) := by
      by_cases h : Charged p f <;> simp [charges,h]
    simp only [split,Finset.sum_add_distrib,List.length_cons]
    exact Nat.add_le_add tail head

theorem neighborhood_tests (R : List Row) (out : V → Finset ℕ)
    (neg : ∀ p, conjunction (wires R) (out p) (outsideN p) = false)
    (pos : ∀ p l, l ∈ N p → conjunction (wires R) (out p) (one l) = true) : 84 ≤ R.length := by
  classical
  have localBound (p : V) : 4 ≤ charges p (history R) := by
    obtain ⟨c,ct,all⟩ := colors p R
    obtain ⟨a,ha⟩ := one_color (mono_and all (out p)) (neg p)
    have sub : (N p).image c ⊆ {a} := by
      intro z hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_singleton.mpr (ha i (pos p i hi))
    have card := Finset.card_le_card sub
    rw [Finset.card_singleton] at card
    rw [neighborhood_size] at ct
    omega
  have safe (f : Wire) (hf : f ∈ history R) : Safe f :=
    safe_wires R f (List.mem_append_right _ hf)
  calc
    84 = ∑ _p : V, 4 := by decide +kernel
    _ ≤ ∑ p : V, charges p (history R) := Finset.sum_le_sum fun p _ => localBound p
    _ ≤ (history R).length := total_charges _ safe
    _ = R.length := history_length R

def eval (R : List Row) (out : Finset ℕ) (x : Input) : Bool :=
  let ws := R.foldl (fun (w : List Bool) (r : Row) => w ++ [
    decide (∀ i ∈ r.1, w.getD i false = true) || decide (∀ i ∈ r.2, w.getD i false = true)])
    (List.ofFn x ++ [false])
  decide (∀ i ∈ out, ws.getD i false = true)
theorem read_wire (ws : List Wire) (x : Input) (i : ℕ) :
    (ws.map (fun f => f x)).getD i false = (ws.getD i zeroWire) x := by
  by_cases h : i < ws.length
  · simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_none (Nat.le_of_not_gt h),zeroWire]

theorem interpret (R : List Row) (out : Finset ℕ) (x : Input) :
    conjunction (wires R) out x = eval R out x := by
  let step (w : List Bool) (r : Row) := w ++ [decide (∀ i ∈ r.1, w.getD i false = true) ||
                                               decide (∀ i ∈ r.2, w.getD i false = true)]
  have same : (wires R).map (fun f => f x) = R.foldl step (List.ofFn x ++ [false]) := by
    induction R using List.reverseRecOn with
    | nil => simp [wires,history,inputWires,zeroWire]
    | append_singleton R r ih =>
      simp only [wires_snoc,List.map_append,List.map_cons,List.map_nil,List.foldl_append,List.foldl_cons,List.foldl_nil]
      rw [← ih]
      simp only [step,gate,conjunction,read_wire]
  change _ = decide (∀ i ∈ out, (R.foldl step (List.ofFn x ++ [false])).getD i false = true)
  rw [← same]
  simp only [read_wire,conjunction]

end PEqualNP.Outside.PlaneNeighborhood

theorem PEqualNP.Outside.plane_neighborhood_sparse_tests :
  let EV := fun (R : List (Finset ℕ × Finset ℕ)) (out : Finset ℕ) (x : Fin 21 → Bool) =>
    let w := R.foldl (fun (v : List Bool) (r : Finset ℕ × Finset ℕ) =>
      v ++ [decide (∀ i ∈ r.1, v.getD i false = true) || decide (∀ i ∈ r.2, v.getD i false = true)])
      (List.ofFn x ++ [false])
    decide (∀ i ∈ out, w.getD i false = true)
  let inc := fun (p l : Fin 21) =>
    ([(p.val+20)%21,p.val,(p.val+5)%21,(p.val+7)%21,(p.val+17)%21] : List ℕ).contains l.val
  let one := fun (l i : Fin 21) => decide (i = l)
  let outside := fun (p l : Fin 21) => !(inc p l)
  ∀ (R : List (Finset ℕ × Finset ℕ)) (out : Fin 21 → Finset ℕ),
    (∀ p l, inc p l = true → EV R (out p) (one l) = true) →
    (∀ p, EV R (out p) (outside p) = false) → 84 ≤ R.length := by
  dsimp only
  intro R out pos neg
  apply PEqualNP.Outside.PlaneNeighborhood.neighborhood_tests R out
  · intro p
    rw [PEqualNP.Outside.PlaneNeighborhood.interpret]
    have outside (p : Fin 21) :
        PEqualNP.Outside.PlaneNeighborhood.outsideN p =
          fun l => !(([(p.val+20)%21,p.val,(p.val+5)%21,(p.val+7)%21,(p.val+17)%21] : List ℕ).contains l.val) := by
      funext l
      simp [PEqualNP.Outside.PlaneNeighborhood.outsideN,PEqualNP.Outside.PlaneNeighborhood.N]
    rw [outside]
    exact neg p
  · intro p l hl
    rw [PEqualNP.Outside.PlaneNeighborhood.interpret]
    exact pos p l (by simpa [PEqualNP.Outside.PlaneNeighborhood.N] using hl)
