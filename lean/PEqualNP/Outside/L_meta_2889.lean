import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The unsigned bound reuses the Base1007 certificate from L-meta-2138.
-- The marked seven-input certificate checks the same restricted signatures with a required NOT.
namespace PEqualNP.Outside.L_meta_2889_aux

namespace Base1007
abbrev B:=BitVec 252
abbrev Sig:=B × B
def top : B:=BitVec.allOnes 252
def zero : Sig:=(0,0)
def one : Sig:=(top,top)
def target : Sig:=(top,0)
def neg (a : Sig) : Sig:=(~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1|||b.1,a.2|||b.2) else (a.1&&&b.1,a.2&&&b.2)
def proper (a : Sig) : Prop:=a ≠ zero/\a ≠ one
def Bz : Sig:=(0x988c662c60004200118004e25321040016c0030d9e4a00039fffd8007000fff,0x988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712)
def GC : Sig:=(0x2130860080010c00060007c01c3e180027000332607ffff2640020007ffffff,0x2130840090850d0886422180040e1a2125221210201110d226222444488a88c)
def GD : Sig:=(0xf88f000070001800070463c0200039fffcc3878c001c78003fff9fff000,0x288f043070431810c6040140208600486843828c4604588c09191234230)
def GE : Sig:=(0xc03f0130000180001ffff8387c07c0003e0000fc07f0001f80003fffe000000,0xc015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8)
def Dw : Sig:=(0x1c001c00001ffffe000003f8007ffffc00000fff800001fffffc0000000000,0x1c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068)
def GF : Sig:=(0xfe0001fffffe00000000003ffff80000000000ffffffffe0000000000000000,0xca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170)
def Be : Sig:=(0xfffffe00000000000000003fffffffffffffff0000000000000000000000000,0xffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80)
def Fo : Sig:=(0xffffffffffffffffffffffc0000000000000000000000000000000000000000,0x35eafe0ade006be01d7807c000000380003800000001c000038007000e00e00)
def raw : List Sig:=[Bz,GC,GD,GE,Dw,GF,Be,Fo]
def Live  (k t : Nat) (S : Finset Sig) : Prop :=
  ∀ (P : Nat → Nat → Finset Sig → Prop),(P 0 0 {target}) →
    (∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (ih : P k t (insert (neg a) U)),P (k+1) (t+1) (insert a U)) →
    (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (ih : P k t (insert (bin d a b) U)),P (k+1) t (insert a (insert b U))) → P k t S
theorem Live.stop   : Live 0 0 {target}:=by
  intro P stop unary binary
  exact @stop
theorem Live.unary  {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) : Live (k+1) (t+1) (insert a U):=by
  intro P stop unary binary
  exact @unary k t U a ha hfresh (tail P stop unary binary)
theorem Live.binary  {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) : Live (k+1) t (insert a (insert b U)):=by
  intro P stop unary binary
  exact @binary k t U a b d ha hb hab hfresh (tail P stop unary binary)
theorem Live.elimInd  {P : Nat → Nat → Finset Sig → Prop}
    (stop : P 0 0 {target})
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) (ih : P k t (insert (neg a) U)),P (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) (ih : P k t (insert (bin d a b) U)),P (k+1) t (insert a (insert b U))) {k t : Nat} {S : Finset Sig} (h : Live k t S) : P k t S:=by
  apply And.right (a:=Live k t S)
  apply h (fun k t S=>Live k t S ∧ P k t S)
  · exact ⟨@Live.stop  ,@stop  ⟩
  · intro k t U a ha hfresh prev
    exact ⟨@Live.unary k t U a ha hfresh prev.1,@unary k t U a ha hfresh prev.1 prev.2⟩
  · intro k t U a b d ha hb hab hfresh prev
    exact ⟨@Live.binary k t U a b d ha hb hab hfresh prev.1,@binary k t U a b d ha hb hab hfresh prev.1 prev.2⟩
theorem Live.elimCases  {P : Nat → Nat → Finset Sig → Prop}
    (stop : P 0 0 {target})
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)),P (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)),P (k+1) t (insert a (insert b U))) {k t : Nat} {S : Finset Sig} (h : Live k t S) : P k t S:=by
  apply Live.elimInd (P:=P) (h:=h)
  · exact @stop
  · intro k t U a ha hfresh prev ih
    exact @unary k t U a ha hfresh prev
  · intro k t U a b d ha hb hab hfresh prev ih
    exact @binary k t U a b d ha hb hab hfresh prev
theorem Live.byInd  {P : ∀ (k t : Nat) (S : Finset Sig),Live k t S → Prop}
  (stop : P 0 0 {target} (@Live.stop ))
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) (ih : P k t (insert (neg a) U) tail),P (k+1) (t+1) (insert a U) (@Live.unary k t U a ha hfresh tail))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) (ih : P k t (insert (bin d a b) U) tail),P (k+1) t (insert a (insert b U)) (@Live.binary k t U a b d ha hb hab hfresh tail)) {k t : Nat} {S : Finset Sig} (h : Live k t S) : P k t S h:=by
  have aux : ∀ hx : Live k t S,P k t S hx:=by
    apply Live.elimInd (P:=fun k t S=>∀ hx : Live k t S,P k t S hx) (h:=h)
    · intro  hx
      exact @stop
    · intro k t U a ha hfresh prev ih hx
      exact @unary k t U a ha hfresh prev (ih prev)
    · intro k t U a b d ha hb hab hfresh prev ih hx
      exact @binary k t U a b d ha hb hab hfresh prev (ih prev)
  exact aux h
theorem Live.byCases  {P : ∀ (k t : Nat) (S : Finset Sig),Live k t S → Prop}
  (stop : P 0 0 {target} (@Live.stop ))
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)),P (k+1) (t+1) (insert a U) (@Live.unary k t U a ha hfresh tail))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)),P (k+1) t (insert a (insert b U)) (@Live.binary k t U a b d ha hb hab hfresh tail)) {k t : Nat} {S : Finset Sig} (h : Live k t S) : P k t S h:=by
  have aux : ∀ hx : Live k t S,P k t S hx:=by
    apply Live.elimCases (P:=fun k t S=>∀ hx : Live k t S,P k t S hx) (h:=h)
    · intro  hx
      exact @stop
    · intro k t U a ha hfresh prev hx
      exact @unary k t U a ha hfresh prev
    · intro k t U a b d ha hb hab hfresh prev hx
      exact @binary k t U a b d ha hb hab hfresh prev
  exact aux h
namespace Theta
def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs
def Run {α : Type} (inv : α->α) (meet join : α->α->α) (y : α) (s : Nat) (ws : List α) : Prop :=
  ∀ (P : ℕ → List α → Prop),(P 0 [y]) →
    (∀ {s : Nat} {xs zs : List α} (p : xs.Perm zs) (ih : P s xs),P s zs) →
    (∀ {s : Nat} {a : α} {rest : List α} (neg save : Bool) (ih : P s ((if neg then inv a else a) :: kept save a rest)),P (s+1) (a :: rest)) →
    (∀ {s : Nat} {a b : α} {rest : List α} (conj ka kb : Bool) (ih : P s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))),P (s+1) (a :: b :: rest)) → P s ws
theorem Run.done {α : Type} {inv : α->α} {meet join : α->α->α} {y : α}  : Run inv meet join y 0 [y]:=by
  intro P done perm one two
  exact @done
theorem Run.perm {α : Type} {inv : α->α} {meet join : α->α->α} {y : α} {s : Nat} {xs zs : List α} (p : xs.Perm zs) (tail : Run inv meet join y s xs) : Run inv meet join y s zs:=by
  intro P done perm one two
  exact @perm s xs zs p (tail P done perm one two)
theorem Run.one {α : Type} {inv : α->α} {meet join : α->α->α} {y : α} {s : Nat} {a : α} {rest : List α} (neg save : Bool) (tail : Run inv meet join y s ((if neg then inv a else a) :: kept save a rest)) : Run inv meet join y (s+1) (a :: rest):=by
  intro P done perm one two
  exact @one s a rest neg save (tail P done perm one two)
theorem Run.two {α : Type} {inv : α->α} {meet join : α->α->α} {y : α} {s : Nat} {a b : α} {rest : List α} (conj ka kb : Bool) (tail : Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))) : Run inv meet join y (s+1) (a :: b :: rest):=by
  intro P done perm one two
  exact @two s a b rest conj ka kb (tail P done perm one two)
theorem Run.elimInd {α : Type} {inv : α->α} {meet join : α->α->α} {y : α} {P : ℕ → List α → Prop}
    (done : P 0 [y])
    (perm : ∀ {s : Nat} {xs zs : List α} (p : xs.Perm zs) (tail : Run inv meet join y s xs) (ih : P s xs),P s zs)
    (one : ∀ {s : Nat} {a : α} {rest : List α} (neg save : Bool) (tail : Run inv meet join y s ((if neg then inv a else a) :: kept save a rest)) (ih : P s ((if neg then inv a else a) :: kept save a rest)),P (s+1) (a :: rest))
    (two : ∀ {s : Nat} {a b : α} {rest : List α} (conj ka kb : Bool) (tail : Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))) (ih : P s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))),P (s+1) (a :: b :: rest)) {s : Nat} {ws : List α} (h : Run inv meet join y s ws) : P s ws:=by
  apply And.right (a:=Run inv meet join y s ws)
  apply h (fun s ws=>Run inv meet join y s ws ∧ P s ws)
  · exact ⟨@Run.done α inv meet join y  ,@done  ⟩
  · intro s xs zs p prev
    exact ⟨@Run.perm α inv meet join y s xs zs p prev.1,@perm s xs zs p prev.1 prev.2⟩
  · intro s a rest neg save prev
    exact ⟨@Run.one α inv meet join y s a rest neg save prev.1,@one s a rest neg save prev.1 prev.2⟩
  · intro s a b rest conj ka kb prev
    exact ⟨@Run.two α inv meet join y s a b rest conj ka kb prev.1,@two s a b rest conj ka kb prev.1 prev.2⟩
theorem Run.elimCases {α : Type} {inv : α->α} {meet join : α->α->α} {y : α} {P : ℕ → List α → Prop}
    (done : P 0 [y])
    (perm : ∀ {s : Nat} {xs zs : List α} (p : xs.Perm zs) (tail : Run inv meet join y s xs),P s zs)
    (one : ∀ {s : Nat} {a : α} {rest : List α} (neg save : Bool) (tail : Run inv meet join y s ((if neg then inv a else a) :: kept save a rest)),P (s+1) (a :: rest))
    (two : ∀ {s : Nat} {a b : α} {rest : List α} (conj ka kb : Bool) (tail : Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))),P (s+1) (a :: b :: rest)) {s : Nat} {ws : List α} (h : Run inv meet join y s ws) : P s ws:=by
  apply Run.elimInd (P:=P) (h:=h)
  · exact @done
  · intro s xs zs p prev ih
    exact @perm s xs zs p prev
  · intro s a rest neg save prev ih
    exact @one s a rest neg save prev
  · intro s a b rest conj ka kb prev ih
    exact @two s a b rest conj ka kb prev
theorem Run.byInd {α : Type} {inv : α->α} {meet join : α->α->α} {y : α} {P : ∀ (s : Nat) (ws : List α),Run inv meet join y s ws → Prop}
  (done : P 0 [y] (@Run.done α inv meet join y ))
  (perm : ∀ {s : Nat} {xs zs : List α} (p : xs.Perm zs) (tail : Run inv meet join y s xs) (ih : P s xs tail),P s zs (@Run.perm α inv meet join y s xs zs p tail))
  (one : ∀ {s : Nat} {a : α} {rest : List α} (neg save : Bool) (tail : Run inv meet join y s ((if neg then inv a else a) :: kept save a rest)) (ih : P s ((if neg then inv a else a) :: kept save a rest) tail),P (s+1) (a :: rest) (@Run.one α inv meet join y s a rest neg save tail))
  (two : ∀ {s : Nat} {a b : α} {rest : List α} (conj ka kb : Bool) (tail : Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))) (ih : P s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) tail),P (s+1) (a :: b :: rest) (@Run.two α inv meet join y s a b rest conj ka kb tail)) {s : Nat} {ws : List α} (h : Run inv meet join y s ws) : P s ws h:=by
  have aux : ∀ hx : Run inv meet join y s ws,P s ws hx:=by
    apply Run.elimInd (P:=fun s ws=>∀ hx : Run inv meet join y s ws,P s ws hx) (h:=h)
    · intro  hx
      exact @done
    · intro s xs zs p prev ih hx
      exact @perm s xs zs p prev (ih prev)
    · intro s a rest neg save prev ih hx
      exact @one s a rest neg save prev (ih prev)
    · intro s a b rest conj ka kb prev ih hx
      exact @two s a b rest conj ka kb prev (ih prev)
  exact aux h
theorem Run.byCases {α : Type} {inv : α->α} {meet join : α->α->α} {y : α} {P : ∀ (s : Nat) (ws : List α),Run inv meet join y s ws → Prop}
  (done : P 0 [y] (@Run.done α inv meet join y ))
  (perm : ∀ {s : Nat} {xs zs : List α} (p : xs.Perm zs) (tail : Run inv meet join y s xs),P s zs (@Run.perm α inv meet join y s xs zs p tail))
  (one : ∀ {s : Nat} {a : α} {rest : List α} (neg save : Bool) (tail : Run inv meet join y s ((if neg then inv a else a) :: kept save a rest)),P (s+1) (a :: rest) (@Run.one α inv meet join y s a rest neg save tail))
  (two : ∀ {s : Nat} {a b : α} {rest : List α} (conj ka kb : Bool) (tail : Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest))),P (s+1) (a :: b :: rest) (@Run.two α inv meet join y s a b rest conj ka kb tail)) {s : Nat} {ws : List α} (h : Run inv meet join y s ws) : P s ws h:=by
  have aux : ∀ hx : Run inv meet join y s ws,P s ws hx:=by
    apply Run.elimCases (P:=fun s ws=>∀ hx : Run inv meet join y s ws,P s ws hx) (h:=h)
    · intro  hx
      exact @done
    · intro s xs zs p prev hx
      exact @perm s xs zs p prev
    · intro s a rest neg save prev hx
      exact @one s a rest neg save prev
    · intro s a b rest conj ka kb prev hx
      exact @two s a b rest conj ka kb prev
  exact aux h
theorem Fd {α β : Type} (e : α->β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e=kept b (e x) (xs.map e):= by cases b <;> simp [kept]
lemma Run.map {α β : Type} (e : α->β) {inv : α->α} {meet join : α->α->α}
    {inv' : β->β} {meet' join' : β->β->β}
    (hi : ∀ a,e (inv a)=inv' (e a)) (hm : ∀ a b,e (meet a b)=meet' (e a) (e b))
    (hj : ∀ a b,e (join a b)=join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e):= by
  induction h using Run.byInd with
  | done=>exact Run.done
  | perm hp _ ih=>exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e):= by
      cases neg <;> simp [Fd,hi]
    rw [e1] at ih;exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)):= by
      cases conj <;> simp [Fd,hm,hj]
    rw [e1] at ih;exact Run.two conj ka kb ih
theorem DT {α inv meet join y s xs} (h : @Run α inv meet join y s xs) : xs.length ≤ s+1:= by
  induction h using Run.byInd with
  | done=>simp
  | perm hp _ ih=>rwa [←hp.length_eq]
  | one _ save _ ih=>cases save <;> simp_all [kept] <;> omega
  | two _ ka kb _ ih=>cases ka <;> cases kb <;> simp_all [kept] <;> omega
abbrev NatRun (m : Nat):=Run (·^^^m) (·&&&·) (·|||·)
lemma q29 {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i=m.testBit j) (hw : ∀ w ∈ xs,w.testBit i=w.testBit j) :
    y.testBit i=y.testBit j:= by
  induction h using Run.byInd with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | one neg save _ ih =>
    apply ih;have ha:=hw _ List.mem_cons_self;intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true,ite_false,ite_true,kept,List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr;exact ha;exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr;simp [ha,hm];exact hw _ (by simp [hr]))
  | two conj ka kb _ ih =>
    apply ih;have ha:=hw _ List.mem_cons_self;have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,ite_false,ite_true,kept,List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons];tauto)
def lo (k : Nat):=2^k - 1
def mask (k : Nat):=lo (k+k)
def goal (k : Nat):=lo k<<<k
def se : Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def q7 : Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def qe : Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000
lemma yx : se=lo 232:= by decide +kernel
lemma vb : q7=mask 232:= by decide +kernel
lemma vc : qe=goal 232:= by decide +kernel
lemma u4 (k i : Nat) : (lo k).testBit i=decide (i<k):= by
  simp [lo,Nat.testBit_two_pow_sub_one]
lemma zn (k i : Nat) : (mask k).testBit i=decide (i<k+k):= by
  simp [mask,u4]
lemma xo (k i : Nat) :
    (goal k).testBit i=(decide (k ≤ i)&&decide (i - k<k)):= by
  simp [goal,Nat.testBit_shiftLeft,u4]
def vd (w : Nat) : Nat:=w^^^(w>>>232)
def s9 : List Nat->Nat | []=>0 | a :: t=>vd a|||s9 t
lemma q11 (i : Nat) (ws : List Nat) : (s9 ws).testBit i=true ↔
    ∃ a ∈ ws,a.testBit i ≠ a.testBit (232+i):= by
  induction ws with
  | nil=>simp [s9]
  | cons a t ih =>
    simp only [s9,Nat.testBit_or,Bool.or_eq_true,ih,vd,Nat.testBit_xor,Nat.testBit_shiftRight,List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (232+i) <;> simp_all
lemma vl {s ws} (h : NatRun q7 qe s ws) :
    (s9 ws&&&se)=se:= by
  rw [vb,vc] at h;rw [yx]
  apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  by_cases hi : i<232
  · have hm : (mask 232).testBit i=(mask 232).testBit (232+i):= by
      simp [zn,show i<464 by omega,show 232+i<464 by omega]
    have hy : (goal 232).testBit i ≠ (goal 232).testBit (232+i):= by
      simp [xo,hi,show ¬ 232 ≤ i by omega]
    have hc : (s9 ws).testBit i=true:= by
      apply (q11 i ws).2;by_contra! hh;exact hy (q29 h i (232+i) hm hh)
    simp [hc]
  · simp [u4,hi]
lemma q34 {m y s ws} (h : NatRun m y s ws) (hl : ws.length=s+1) (i j : Nat)
    (hw : ∀ a ∈ ws,a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j:= by
  induction h using Run.byInd with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (hp.length_eq.trans hl) (fun a ha=>hw a (hp.mem_iff.1 ha))
  | one _ save h _=>have hh:=DT h;cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh:=DT h;cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept];omega)
    have ha:=hw _ List.mem_cons_self;have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had;simp only [kept,Bool.false_eq_true,ite_false,List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true,Bool.false_eq_true,ite_false,Nat.testBit_or,Nat.testBit_and] <;> grind
    · exact hw _ (by simp [ht])
def sq (w : Nat) : Nat:=(w>>>232)&&&(w^^^se)
def rd : List Nat->Nat | []=>0 | a :: t=>sq a|||rd t
lemma zu (i : Nat) (hi : i<232) (ws : List Nat) : (rd ws).testBit i=true ↔
    ∃ a ∈ ws,a.testBit i=false/\a.testBit (232+i)=true:= by
  induction ws with
  | nil=>simp [rd]
  | cons a t ih=>simp [rd,sq,yx,u4,hi,ih,and_comm]
lemma rl {s ws} (h : NatRun q7 qe s ws) (hl : ws.length=s+1) :
    (rd ws&&&se)=se:= by
  rw [vb,vc] at h;rw [yx]
  apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  by_cases hi : i<232
  · have hy : ¬ (goal 232).testBit (232+i) ≤ (goal 232).testBit i:= by
      simp [xo,hi,show ¬ 232 ≤ i by omega]
    have hc : (rd ws).testBit i=true:= by
      apply (zu i hi ws).2;by_contra! hh;apply hy
      apply q34 h hl;intro a ha;specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (232+i) <;> simp_all
    simp [hc]
  · simp [u4,hi]
lemma y1 {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys):= by cases b <;> simpa [kept] using p
def vy (s : Nat) (ws : List Nat) (f : Bool->List Nat->Bool) : Bool :=
  let len:=ws.length
  let slack:=s+2 - len
  let t0:=decide (len=s+2)
  let t1:=decide (len=s+1)
  let t2:=decide (len=s)
  ws.any fun a =>
    let ra:=ws.erase a
    let da:=vd a
    let dau:=sq a
    (slack ≥ 1 &&
      (let cra:=if t1&&slack==1 then 0 else s9 ra
       let crau:=if t1||t2 then rd ra else 0
       [false,true].any fun neg =>
        let w:=if neg then a^^^q7 else a
        (((if t1 then sq w|||crau else vd w|||cra)&&&se==se)&&f t1 (w :: ra)) ||
        (slack ≥ 2 &&
          ((if t2 then sq w|||(dau|||crau) else vd w|||(da|||cra))&&&se==se) &&
          f t2 (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b &&
      (let r:=ra.erase b
       let db:=vd b
       let dbu:=sq b
       let cr:=if t0 then 0 else s9 r
       let cru:=if t0||t1||t2 then rd r else 0
       [false,true].any fun conj =>
        let w:=if conj then a&&&b else a|||b
        let dw:=if t0 then 0 else vd w
        let dwu:=if t0||t1||t2 then sq w else 0
        (((if t0 then dwu|||cru else dw|||cr)&&&se==se)&&f t0 (w :: r)) ||
        (slack ≥ 1 &&
          ((((if t1 then dwu|||(dau|||cru) else dw|||(da|||cr))&&&se==se)&&f t1 (w :: a :: r)) ||
           (((if t1 then dwu|||(dbu|||cru) else dw|||(db|||cr))&&&se==se)&&f t1 (w :: b :: r)))) ||
        (slack ≥ 2 &&
          ((if t2 then dwu|||(dau|||(dbu|||cru)) else dw|||(da|||(db|||cr)))&&&se==se) &&
          f t2 (w :: a :: b :: r)))
lemma q08 {a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun q7 qe s ((if neg then a^^^q7 else a) :: kept save a rest))
    (f : Bool->List Nat->Bool) (hf : ∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true) :
    vy s ws f=true:= by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a):=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hh:=DT h;have hl:=p.length_eq;simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length:= by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩;rw [Bool.or_eq_true];left
  rw [Bool.and_eq_true];refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have hrun:=Run.perm ((y1 pr save a).cons _) h
  have ht:=hf _ hrun
  have hcov:=vl hrun
  cases save with
  | false =>
    simp only [kept,Bool.false_eq_true,ite_false] at ht hrun hcov
    have hlen : ((if neg then a^^^q7 else a) :: ws.erase a).length=ws.length:= by
      simp [List.length_erase_of_mem ha];omega
    rw [hlen] at ht
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,Bool.true_or,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h1,decide_false,Bool.false_and,s9] at ht hcov ⊢
      simp [hcov,ht]
  | true =>
    simp only [kept,ite_true] at ht hrun hcov
    simp only [kept,ite_true,List.length_cons] at hh
    have hsl2 : 2 ≤ s+2-ws.length:= by omega
    have hlen : ((if neg then a^^^q7 else a) :: a :: ws.erase a).length=ws.length+1:= by
      simp [List.length_erase_of_mem ha];omega
    have hlen_eq : decide (((if neg then a^^^q7 else a) :: a :: ws.erase a).length=s+1)=decide (ws.length=s):= by
      rw [hlen];exact decide_eq_decide.mpr (by omega)
    rw [hlen_eq] at ht
    by_cases h2 : ws.length=s
    · have hcu:=rl hrun (by omega)
      simp only [h2,decide_true,Bool.or_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · have h1 : ws.length ≠ s+1:= by omega
      simp only [h1,h2,decide_false,Bool.false_and,s9] at ht hcov ⊢
      simp [decide_eq_true hsl2,hcov,ht]
lemma u9 {a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun q7 qe s ((if conj then a&&&b else a|||b) :: kept ka a (kept kb b rest)))
    (f : Bool->List Nat->Bool) (hf : ∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true) :
    vy s ws f=true:= by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pp:=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hb:=pp.mem_iff.1 List.mem_cons_self
  have pr:=(pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh:=DT h;have hl:=p.length_eq;simp only [List.length_cons] at hl hh
  have hlenr : ((ws.erase a).erase b).length=ws.length - 2:= by
    have:=pr.length_eq;omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩;rw [Bool.or_eq_true];right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩;rw [Bool.and_eq_true];refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have hrun:=Run.perm ((y1 (y1 pr kb b) ka a).cons _) h
  have ht:=hf _ hrun
  have hcov:=vl hrun
  cases ka <;> cases kb
  · simp only [kept,Bool.false_eq_true,ite_false] at ht hh hrun hcov
    have hlen : ((if conj then a&&&b else a|||b) :: (ws.erase a).erase b).length=ws.length - 1:= by
      simp [hlenr];omega
    have hle : decide (((if conj then a&&&b else a|||b) :: (ws.erase a).erase b).length=s+1)=decide (ws.length=s+2):= by
      rw [hlen];exact decide_eq_decide.mpr (by omega)
    rw [hle] at ht
    by_cases h0 : ws.length=s+2
    · have hcu:=rl hrun (by omega)
      simp only [h0,decide_true,Bool.true_or,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,decide_false,s9] at ht hcov ⊢
      simp [hcov,ht]
  · simp only [kept,Bool.false_eq_true,ite_false,ite_true] at ht hrun hcov
    simp only [kept,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at hh
    have hsl1 : 1 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: b :: (ws.erase a).erase b).length=ws.length:= by
      simp [hlenr];omega
    rw [hlen] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h1,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl1,hcov,ht]
  · simp only [kept,Bool.false_eq_true,ite_false,ite_true] at ht hrun hcov
    simp only [kept,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at hh
    have hsl1 : 1 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: a :: (ws.erase a).erase b).length=ws.length:= by
      simp [hlenr];omega
    rw [hlen] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h1,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl1,hcov,ht]
  · simp only [kept,ite_true] at ht hrun hcov
    simp only [kept,ite_true,List.length_cons] at hh
    have hsl2 : 2 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: a :: b :: (ws.erase a).erase b).length=ws.length+1:= by
      simp [hlenr];omega
    have hle : decide (((if conj then a&&&b else a|||b) :: a :: b :: (ws.erase a).erase b).length=s+1)=decide (ws.length=s):= by
      rw [hlen];exact decide_eq_decide.mpr (by omega)
    rw [hle] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h2 : ws.length=s
    · have hcu:=rl hrun (by omega)
      simp only [h2,decide_true,Bool.or_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h2,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl2,hcov,ht]
lemma q07 {a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun q7 qe s ((if conj then a&&&b else a|||b) :: kept ka a (kept kb b rest)))
    (f : Bool->List Nat->Bool) (hf : ∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true) :
    vy s ws f=true:= by
  rcases le_total a b with hab | hba
  · exact u9 hab p h f hf
  · apply u9 (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a&&&b else a|||b)=(if conj then b&&&a else b|||a):= by
      cases conj <;> simp [Nat.and_comm,Nat.or_comm]
    rw [he] at h;apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept];exact List.Perm.swap _ _ _
lemma q1f {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t=0->ws=[y]:= by
  induction h using Run.byInd with
  | done=>simp
  | perm p _ ih=>intro ht;rw [ih ht] at p;exact List.perm_singleton.1 p.symm
  | one=>simp
  | two=>simp
lemma y0 {t ws} (h : NatRun q7 qe t ws) :
    ∀ s,t=s+1->∀ zs,ws.Perm zs->∀ f : Bool->List Nat->Bool,
      (∀ ys,NatRun q7 qe s ys->f (decide (ys.length=s+1)) ys=true)->vy s zs f=true:= by
  induction h using Run.byInd with
  | done=>simp
  | perm p _ ih=>intro s he zs q;exact ih s he zs (p.trans q)
  | one _ _ h _=>intro s he zs p f hf;cases he;exact q08 p h f hf
  | two _ _ _ h _=>intro s he zs p f hf;cases he;exact q07 p h f hf
def xs517 : List ℕ:=[0xf4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517,0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827,0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248,0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0,0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418,0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800,0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688]
lemma yn : ∀ zs ∈ xs517.sublists,zs ≠ xs517 →
    (s9 zs&&&se) ≠ se:= by decide +kernel
def r2 (tag d w : Nat) : Nat:=((w&&&tag)<<<d)|||((w>>>d)&&&tag)
lemma q3l (tag d i w : Nat) (h : (tag&&&(tag<<<d))=0) :
    (r2 tag d w).testBit i =
      (if tag.testBit i then w.testBit (d+i)
       else if (tag<<<d).testBit i then w.testBit (i-d) else false):= by
  have ht:=congrArg (fun v : Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  simp only [r2,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,Nat.testBit_shiftRight] at *
  by_cases hi : d ≤ i <;> simp [hi] at*<;> grind
lemma yw (tag d : Nat) (h : (tag&&&(tag<<<d))=0) (a b : Nat) :
    r2 tag d (a&&&b)=(r2 tag d a&&&r2 tag d b) ∧
    r2 tag d (a|||b)=(r2 tag d a|||r2 tag d b) ∧
    r2 tag d (a^^^b)=(r2 tag d a^^^r2 tag d b):= by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,q3l tag d i _ h] <;>
    split_ifs <;> simp
lemma q0b {s ws} (h : NatRun q7 qe s ws) (tag d : Nat)
    (hz : (tag&&&(tag<<<d))=0) (hm : r2 tag d q7=q7)
    (hy : r2 tag d qe=qe) :
    NatRun q7 qe s (ws.map (r2 tag d)):= by
  rw [← hy]
  exact Run.map _ (fun a=>(yw tag d hz a q7).2.2.trans (by rw [hm]))
    (fun a b=>(yw tag d hz a b).1) (fun a b=>(yw tag d hz a b).2.1) h
def q3e : Nat:=0x3ffffffffffffff000000000000003ffffffffffffff000000000000003ffffffffffffff000000000000003ffffffffffffff
def q3d : Nat:=0xfffffffffffffffffffffffffffff00000000000000000000000000000fffffffffffffffffffffffffffff
def q38 (xs : List Nat):=xs.map (r2 q3e 58)
def q37 (xs : List Nat):=xs.map (r2 q3d 116)
lemma q3j {s ws} (h : NatRun q7 qe s ws) : NatRun q7 qe s (q38 ws) :=
  q0b h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
lemma q3i {s ws} (h : NatRun q7 qe s ws) : NatRun q7 qe s (q37 ws) :=
  q0b h _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
def vf (a b c d e f : Bool) : Nat :=
  let x:=b.toNat+c.toNat;let y:=(!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)
lemma q0q : ∀ a b c d e f g h i j l m : Bool,
    vf (a&&g) (b&&h) (c&&i) (d&&j) (e&&l) (f&&m)
      ≤ vf a b c d e f+vf g h i j l m:= by decide +kernel
lemma q1g : ∀ a b c d e f g h i j l m : Bool,
    vf (a||g) (b||h) (c||i) (d||j) (e||l) (f||m)
      ≤ vf a b c d e f+vf g h i j l m:= by decide +kernel
lemma q05 {l r : List Nat} (h : l.Perm r) : l.sum=r.sum:= by
  induction h with
  | nil=>rfl
  | cons _ _ ih=>simp [ih]
  | swap=>simp;omega
  | trans _ _ ih1 ih2=>exact ih1.trans ih2
lemma q01 {m y s ws} (h : NatRun m y s ws) (hl : ws.length=s+1)
    (v : Nat->Nat) (hand : ∀ a b,v (a&&&b) ≤ v a+v b)
    (hor : ∀ a b,v (a|||b) ≤ v a+v b) : v y ≤ (ws.map v).sum:= by
  induction h using Run.byInd with
  | done=>simp
  | perm p _ ih=>rw [← q05 (p.map v)];exact ih (p.length_eq.trans hl)
  | one _ save h _=>have hh:=DT h;cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh:=DT h;cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih':=ih (by simp [kept];omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc,← hand];exact ih' | grw [← Nat.add_assoc,← hor];exact ih'
def yz (a b c d e f v : Nat) : Nat :=
  if v.testBit a then
    if v.testBit d then (!v.testBit e).toNat+(!v.testBit f).toNat
    else
      let x:=(v.testBit b).toNat+(v.testBit c).toNat
      let y:=(!v.testBit e).toNat+(!v.testBit f).toNat
      max x (max y (x+y - 1))
  else
    if v.testBit d then 0
    else (v.testBit b).toNat+(v.testBit c).toNat
lemma q0e (a b c d e f v : Nat) :
    yz a b c d e f v=vf (v.testBit a) (v.testBit b) (v.testBit c)
      (v.testBit d) (v.testBit e) (v.testBit f):= by
  unfold yz vf
  cases v.testBit a <;> cases v.testBit d <;> rfl
lemma q0f {m y s ws} (h : NatRun m y s ws) (hl : ws.length=s+1)
    (a b c d e f : Nat) : yz a b c d e f y ≤ (ws.map (yz a b c d e f)).sum:= by
  apply q01 h hl
  · intro v w;simp only [q0e,Nat.testBit_and];exact q0q _ _ _ _ _ _ _ _ _ _ _ _
  · intro v w;simp only [q0e,Nat.testBit_or];exact q1g _ _ _ _ _ _ _ _ _ _ _ _
def q26 : List (Nat × Nat × Nat × Nat × Nat × Nat) :=
  [(462,447,452,215,221,207),(453,441,440,220,193,181),(445,410,360,199,216,201),(460,410,440,178,229,217),(459,461,454,220,89,205),(370,438,302,215,216,211),(457,410,418,199,207,201),(403,428,450,207,201,220),(457,429,450,218,207,201),(456,452,454,219,201,199)]
lemma zy : q26.all (fun t =>
    yz t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 qe==3)=true:= by decide +kernel
def yh (a b c d e f : Nat) : Nat->List Nat->Bool
  | acc,[]=>decide (acc<3)
  | acc,w :: t =>
    let acc':=acc+yz a b c d e f w
    if acc' ≥ 3 then false else yh a b c d e f acc' t
lemma zo (a b c d e f : Nat) (ws : List Nat) (acc : Nat)
    (h : yh a b c d e f acc ws=true) : acc+(ws.map (yz a b c d e f)).sum<3:= by
  induction ws generalizing acc with
  | nil=>simpa [yh] using h
  | cons w t ih =>
    simp only [yh] at h
    split at h
    · contradiction
    · have ih':=ih _ h
      simp only [List.map_cons,List.sum_cons]
      omega
def q0x (ws : List Nat) : Bool :=
  q26.any (fun t=>yh t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 0 ws)
lemma q1n {s ws} (h : NatRun q7 qe s ws) (hl : ws.length=s+1) :
    q0x ws=false:= by
  rw [Bool.eq_false_iff];intro hk
  obtain ⟨t,ht,hlt⟩:=List.any_eq_true.mp hk
  have hg:=beq_iff_eq.mp (List.all_eq_true.mp zy t ht)
  have hb:=q0f h hl t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2
  have hs:=zo t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 ws 0 hlt
  rw [hg] at hb;omega
def span (f : Nat->Bool) : Nat->Nat->Bool
  | 0,_=>true
  | n+1,i=>f i&&span f n (i+1)
theorem span_ok {f n o} (h : span f n o=true) : ∀ i,o ≤ i->i<o+n->f i=true:= by
  induction n generalizing o with
  | zero=>omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h;intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)
theorem span_join {f a o b} (ha : span f a o=true) (hb : span f b (o+a)=true) :
    span f (a+b) o=true:= by
  induction a generalizing o with
  | zero=>simpa using hb
  | succ a ih =>
    simp only [span,Bool.and_eq_true] at ha;rw [Nat.succ_add,span,Bool.and_eq_true]
    exact ⟨ha.1,ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩
lemma q10 {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r):= by
  induction t,hle using Nat.le_induction with
  | base=>exact h
  | succ _ _ ih=>exact Run.one false false ih
def q36 : Nat->Nat
  | 0=>0xf4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b91251724386c0009da09c90e1b0002768270350420a044145c0d410828110517
  | 1=>0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a0350420a044145c0d41082811051724386c0009da09c90e1b000276827
  | 2=>0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c808390c5d024922020e4317409248808390c5d024922020e4317409248
  | 3=>0x6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3004002ba9605a20001c441a981418000dbd45209a0000282330446c2e0
  | 4=>0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238000dbd45209a0000282330446c2e0004002ba9605a20001c441a981418
  | 5=>0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a688000071106a60506001000aea58168800a08cc111b0b800036f514826800
  | 6=>0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e8800a08cc111b0b800036f51482680000071106a60506001000aea581688
  | 7=>0
  | 8=>q7
  | 9=>0x6f27d5b39727ae1b49f56d29a9e3808d7be5d22ba78c2bdef96c46fbe3004202ba9605a60011c4cfa98141800adbd4521ba18002a2b30446eae0
  | _=>0xff28d8b3df67b7254ff5613bb923c9858b85d6afa3524efe7b0f67d3e780c202bad625b22001c441b981418808fbd4560ba1020282330546c2e0
def q24 : Nat->Nat
  | 0=>0x2e0060280e268192c8192a0162b81918806200192a019000081000503005188191880917801268a50013001001001280180a1481912811230110080214811218110300219811200110280616805020051e015000ec018011c8151481a16819178151a8150300a1981503006188150000017809030121680902812000ac01802148150000c10009118191281501006118150200a0b80910011030160f0150200602811098010d001028050a8050b811030150a8090280d098090300d08805028090780503011068050200d0580502009
  | 1=>0xb80e01806419520b952099521f152549510004c1d812531e91f00e520163d00d33951231511d8160027c00801000044e01601805268052a005380a51881610012421b2498fa3601206816188121f0c6068c62b0121e15129012380c50022801002440c5001482481242812030010b8120011829016308161f016078163e81a01809338c5001e802002188053081a1f01a178050581a0e81a0881a0d01a38019001bc0100536819001b0028011e0193481920002338190003432819320060280a3101900184020012f819168062e819
  | 2=>0x378a62080a1f00a1b80a0b80a0780a0d00a0d80a0c00a7ca290e80a0800a0700a7a80900074368096a132338097800914806230090b8a60d0a6260a61f0a6748a500068368a5730a50005c001703d0a514801708a5000f8002e8440a50030414809378c637812378161e0056b8051780a3781a1180519809200093200514805378013b00e2b00e2980e590ad1f80e530ad612e93d80e581b21a00e3c80e1100e613052600e0300e5d9b25eae95e9293600e5dae90d00e0200e0c00e580ad0900e0d80e0800e0600e591292900e582bd
  | _=>0x5e9327780e001f4000185200a9e8fa000540001412802000102b0023b002290026a802378021d80a0b80214802110029fc691f0029ec6906802090020c0020800207002060022a00652006591be6a80e6900e3780e6800e1d806002701a806260064f80a1780606806100060a806360060b80692006030090880642806078060e806730054f81a450053d0058d005028021680a1880a778124180a0680a148126e812260121000a778163600a14816360a6260163d8a63b00a2b00a2900a2880a0980a290a61480a
def zf : Nat->Nat->Nat
  | 0,_=>0
  | fuel+1,i =>
    if i<11 then q36 i
    else
      let k:=i - 11
      let c:=(q24 (k/83)>>>(20*(k % 83)))&&&1048575
      let op:=c&&&3
      let a:=(c>>>2)&&&511
      if op=0 then zf fuel a^^^q7
      else let b:=c>>>11;if op=1 then zf fuel a&&&zf fuel b else zf fuel a|||zf fuel b
def q2a : Nat->Nat
  | 0=>0x181dc00005ff70000179dc00005ef70000175dc00005cf70000171dc00005bf7000016ddc00005af70000169dc00005977000022fec000085fb004b86de40000857b0000211ec000081fb0050205e80000817b0000203ec0144807a0000201ec00007d7b00001fbec00007e7b00001f7ec00007cfb00001f1ec008b977c3d91c83f0014493fc0000295f80000a4fe000028ff80000a37e0000289f80000a07e0000285f80000a0fe000027ff800009efe0000279f800009dfe0000275f800009cfe0000001fc0000907d00001efec00007afb00001e9ec000079fb00001e5ec0146787a00001e1ec00006efe00001b5f400006cfd000015fec0000577b000015bec0000567b0030cabcc01332af3000a8abcc00b32af30029cabcc00b12af3002f8abcc00bc2af300518abe801442afa00500abe800002afb0000157ec0000527b0000147ec00c34ff5004cd3fd4002a4ff5002cd3fd400a74ff5002c53fd400be4ff5002f13fd454554ff10000139f400004d770000125f8000048fe0030c65d801331976000a865d800b319760029c65d800b119760031865d800be1976002f065d80110197a0042065e80102197a0040065e800fa197a004b865f00128197c0049c65f00000197e003c065e8545519720015465e8549f19740027c65f0aa9f1978000011fec000046fe0000115f800003efe0011ceff40000393f00000defc0000363f00000d6fc000034bf00000cefc0000323f00000c2fc00002fbf00000b8fc00002dbf00154b6ec00002cbf000c8b2f8014d2b9f00194ae7c005d2b9f0020cae7c014b2baf00240aebc002a2bb70033caedc010a2bbb0049caef4014a2bbe00000aefc00552bbb0027caef400322bbe000009fdc013e1fee002947f9c00001f5f000a8775c00001ddf328d8306c00be0c5700440316c011888cb00435b92c00c84bc70053d2d3801375355004f94d58012b515525cf8498801538c630030db98c013754e500001519c01509bf10051657c401509f720054e8dc8004785f9002f8ae5c01102b9b
  | 1=>0x45fc014b086f000c021bc002a08770000021fc0055087b0027c21f40032087e0000041fc014b0f6f000b83dbc002a0f77003e83dec00000f7f001543dec00320f7e0054436fc014d0ddf00104377c014b0def000a837dc00bc0df70010437f400000dff0015437ec009f0dfd000c837f800000eff0000039fc00000d7f0000033fc00000bff000002bfc000009ff0000023fc000007ff000001bfc002a04770000011fc0055047b000c811fa9b4b154700536973c014d6e4f0052db73c00dc6dcfa6d2cab2e9b4b194e005351d3c014d43cf005350b3c005d42cf0030e1b5c014d155700434555c01336dd7000a9b75e9a2a2ad3000b1455c00b05157000a9455e9a2a4fd5002c13d5c002a4f57000a9295e9a2a19560052d073c008e41cf000a9075c007b40cf0052d033c002a40d70029d035c014b156700450559c01131567004cdb99c002a6e67a58a8ab8c00b054e7000a9539c002a4ae7a58a86598002a4767002cd1d9c002a4467000a90f9c002a42e7002c50b9c00c345f3000b28bcc014558730030c49cc00c31b730030e5dd4004b95f50012e7dd80000aa7700002a7dc000061f70000017dc00009b77000026bdc00009a770051a67d8000099f70000265dc000087770000219dc000083770000209dc0153787300001dfdc0000777700001dbdc000076770051455cc011615730044055cc010915730041c55cc010215730040055cc00fa1573004c455d4012e1575004ac55d4012815750049c55d4013e15760052055d8014615760051055d8014015760000055dc00f21573003c055cc000075f700001d3dc0000747700001cbdc000071f700001c1dc00c3387300001a1dc000067f7000019ddc010959f30052167d8000059f7000019bdc012b5df50000199dc010253f30007d4fd4014053f6000014fdc000065f70000195dc000064f7004acbbd4013e2ef60000191dc00000577000018fdc010058f30049d63d4014458f60000163dc00006377000018bdc000062770000183dc01105f73004a17dd400005f77
  | 2=>0x1a5fc000068ff000009dfc00002d7f000a8abcc002a2af700024abec00472afb00000abec01382afb00098abec00412afb000d0abec00022afb00280abec00362afb00000abfc002a2afb001c0abec005a2afb00154abec000050ff000a93fd4002a4ff70000137fc00554dfb0000133fc00004c7f000a85ddc0047177f000005dfc0055177b0000127fc002a1977000a865d80009197e0011c65f8014b197e0011065f8008b197e0046c65f80000197f0009865f80058197e0010465f80034197e0000865f80000197e0028065f80119197e0019465f80036197e0000c65f8002a197e0013465f80070197e0015465ec0055197a0015465f8009f197e0027c65f00099197e000b865f80093197e000c865f8002a18770011c61fc0000187f0015461ec009f187d000c861f80000467f000010bfc0000427f000a843dc000010ff0015443ec003210fe0000107fc0000417f0000103fc0000407f00000fffc00003e7f00000f5fc00323d7e00000f3fc00003c7f00000effc00003b7f00000ebfc00003a7f00000e7fc014d03df0052c0fbc002a03f7000000ffc005503fb0027c0ff4003203fe00000aefc00412bbf00000affc00002b7f00154adec00002a7f00000a5fc0032297e00000a3fc003228fe00000a1fc0000267f000a895dc0000257f0000093fc0000247f000a88ddc0000237f000008bfc000021ff0000085fc0000207f005447efc00781fbf005347f7c00811fdf001ec7fbc014b1fef0007c7fbc002a1ff70029c7fdc01021ffb0007c7ff401401ffe000007ffc00551ffb0027c7ff400321ffe0000073fc00001c7f000006ffc00001aff0000067fc003219fe00534317c00650c5f00174317c00210c5f000a831dc00b10c770040031ec01440c7e0000031fc00550c7b000c831f800530c3f0000063fc000017ff000005bfc002a15f70000057fc000014ff0000051fc000013ff000004bfc0151093f00534257c0065095f0052c25bc002a09770019425ec0000097f0015425ec009f097d000c825f8000011ff
  | _=>0x7f0000055dc000023ff0000001fc0000137f0000083fc00001a7f0000005fc0000507f000006dfc000001ff0000055fc0000387f00000abec00002aff000005dfc0000197f0000065f80000187f0000043fc000003ff000007ffc00000c7f0000025fc0000087f000003dfc00000dff00536973c014d15570052c559c002c25f70000187dc004b58770000267dc00091577000b055dc004b15770054455dc007b15770053455dc004715770052c55dc004415770022c55dc011b15770050c55dc000115770000055dc00b01577003c455dc002615770007c55dc00411577000d055dc000215770028055dc002415770045455dc006515770043c55dc00361577000e855dc010515770000c55dc002a1577000a9c9dc002a6f770030c9bdc002a26f7004cce1dc002a3877000a9a5dc00b06177000a985dc000059f7002c177dc002a5df7000014fdc002c2ef7002c0bbdc002a2ef700308bbdc000058f7000017ddc00005e770012c6dec00261b7b001946dec0000817b0000201ec00007d7b0011c89f8004745fe000028df800448dfe0000289f80000a07e0000013fc0000a97f0000155fc0000a77f00000d5fc0000347f0000299fc000023ff0000287fc0000007f00000bdfc00009c7f0000261fc0000337f000025ffc000078ff000004dfc0000977f000025bfc0000307f0000259fc00002c7f0000255fc007b20ff0000083fc000094ff0000251fc00001a7f000024ffc0000937f0000249fc000091ff0000245fc000090ff0000005fc00008fff000023dfc00008eff0000239fc0047507e0000141fc00008d7f000007bfc00006c7f0000233fc00008aff0000225fc000087ff000006dfc00001d7f000020bfc0000817f0000201fc00007fff00001fdfc00007d7f0000007fc0047787b00001e1ec0000787f0000055fc0000737f00001c9fc000070ff00001bffc00006f7f00001b7fc00006bff00001adfc00006aff00001a9fc000069ff00098e1ec0065387b00098e1f40146387e00000e1fc004d387b
def xl (code k : Nat) (acc : List Nat) : List Nat :=
  if (code>>>k)&&&1==1 then q36 k :: acc else acc
def z0 (e : Nat) (acc : List Nat) : List Nat :=
  if e==0 then acc else zf 4 (e - 1) :: acc
def q3k (i : Nat) : List Nat :=
  if i<6 then []
  else
    let j:=i - 6
    let code:=(q2a (j/176)>>>(34*(j % 176)))&&&0x3ffffffff
    let acc:=z0 ((code>>>25)&&&511) (z0 ((code>>>16)&&&511) (z0 ((code>>>7)&&&511) []))
    xl code 0 (xl code 1 (xl code 2 (xl code 3 (xl code 4 (xl code 5 (xl code 6 acc))))))
def q25 : Nat->Nat
  | 0=>1 | 1=>1 | 2=>1 | 3=>1 | 4=>1 | 5=>1
  | 6=>19 | 7=>292 | 8=>365 | 9=>26 | 10=>1 | _=>0
def q3t : Nat->Nat
  | 0=>0 | 1=>1 | 2=>2 | 3=>3 | 4=>4 | 5=>5
  | 6=>6 | 7=>25 | 8=>317 | 9=>682 | 10=>708 | _=>0
def vj (s i : Nat) : List Nat:=q3k (q3t s+i)
def sg (salt : Nat) : List Nat->Nat
  | []=>0
  | w :: t=>let x:=(w % 1048573+317+salt) % 1048573;(x*x*x) % 1048573+sg salt t
def q18 : Nat->Nat
  | 6=>0x2d510a29c920dd8c26046a45edcab10e217235801e802cc829b
  | 7=>0xba020271000f0d789715b90b1b40d05ca2d4a2b20600798bac5c7e51085e9a4554cdd8e3980600005246e24e7704c2f50005cd6d23c0e8ee0943e87206f17bbbe2205918c9ad6d8c4dd10000ca1d4a0086754ac52a4592ac768220bc3fc1f922c761b4a30630003be5e00833f0d0d88b41f41811e4783cf36e2dc004002e0fbd5d8007d4b20a617c1680000029e1429da3348d12e9adfc1e03a65ca0c0b8279042040b6832081c4a94630e90120006c8e7618c585e8478000000e0b5e3abee6724d0dc28a4f63f1783c6676dd56abce0000e08019e42acc8c20d74cc7606228d6fa4e030800778001c584c7764b0a4ac49105d1a648c4486522847d50cc6e20a0c4d4e35f0901710e0cf40515302009b2095a0370e248f4c04163a3ab0e2840000aa000b85763445f112a350607800000029000006d184643c45988fb302401912822c64a9d0e0251912f598a0f42b8671a88181a41b0d04218a2434643e58a8f31b8394262fda061372b12394e130690d75503ca3d8870b697b212c6a301b50092181d0146e85e85835b2103bcf84497750e5ff1886ee6a8460501e2ebd824067cd205840001d91dcb18003c8b01d480c8280d067c358d0e1c820064b038188b0c722360a82b46ecd1d3fb780008508e3d453439e0ab8c320211da96c49235238a77476931a93a75666c63f3553f2880e4054184a210f404408b042709674c3e1af888398a483c3b7302460aa0ba8f06319693b13a3a09d00888a0a912af60582b10c1d65990a588472078ca40e9987a0801342287b47757e41d838d2941b3c228ff1c54020aac9092059006afd1a425090c482c4850b8cf9379f87621756ebdc27d118652a69049007e8914bf0f0b012a684ab49f802050ea22623a
  | 8=>0x138c54934604ac03d9da53893a963200001f918326961401461089814d14c94c238451f64d35929b4ffaf00002f2588000001a6d1c3b8e552048160000c7da4508a12ea26db16296bd4174c85145c2c45633c2b20c82402f83540b8c291ccda0a2c69e6c9eca21c2a0b32380b2a0ac60a180095d0bdd04b246a3d513ace3aa972874da6d12706ca58000a1009a100ee43944337528b29fa491af5485ec98a38a278ca0421a2b04903aa0829c0915225ecb49060815d8002cecf16671685a93052a10eaaae5249586bf0f0aeca69a030a2190e0e420b1707a822828a486a0ae27e4f50b56214a3320d56cc656d4d911c53d81c0725307c8d2be5faaad16f4d8a258091347291cdca1ed5dec5685f09208d2be2b0f502b18c1101fd8bd580c6170a10af63b6318d13b231385cca428188a62b26c28e949168927081b0890e0aba9e0040269400f2c59014d6670b590016363c59c58138de07c8391f105e2808a0c869d46aed6a82117f42080ed12ba0f4b08151da27cb0f180e20dc9fc0023e5a74085eeb944fafa110bfa19830b40f68686160013b2a22082398f4d442f04a620c4000002211d407031a26c888514480034f1ec65800402a400009c1dd13a932c83919f0c00c2376858002822bc3b9462330991510e6a11296a7530cb8219c518464554899170005ac7f05a12d2600002d1fe000000ac43043324a781ff1c1670760b312c69b2299d1e869c551c62a085d028515a82d93ea730a41d9582a81a063800064be426b5cda8b35174b0a59ccc19eb0245b5245d516d8cf57e4544e80150494c2cf8955b0486364e79f2176764c5478cc4ba000900101ed355380392a1d0c118ee1e423a000d31ba36028c1d118b2471a0c4a48007988d1162e80315e2742680a1598944bc9701e1a83102201b47e05816d544fc03083d4a2082920003001556e38c3f44a4407c0b76562d488805032b9427aaa016464000c1819282a82a618a37e140351d5b805d33781b1956d8ad29e01d930119822ac0560012e9fb018131e24d99695c1669c70006f92a2f4950b72cc325400c21231616587088b0ae90ab9002000855500f60005c2a99970ac8911b97e567000260a0514712600cc4367782c01f106669099ad2f73c6dc179d7f360515401b83e8990e65933865e276a50ac4592ae0cc5c09959456c2e2ea5d640f052e4008538372c1ca41de619665ae3b03b725475bc0369359ab3324d26b08f0005715f1e84df000cf83393c7b87923c256875510243753e0a908db9dac89d023a20b44cc289be83c53bec083f3780ccda9df0013f63a4a274ca400001181acf03821d7b6c547d43c
  | 9=>0xa197f9864cac828bcc96272d000622a0801403cb48d000b1ebd4114d11504f80408a7451700016502d6981bb801d1148e240e1f1b0344d9ea8d30f4e10
  | _=>0
def q17 : Nat->Nat
  | 6=>0x6d235ea20
  | 7=>0x234342c80020021d2500aec0506cac86608011a05070243405480089c0601bd838e5329f00e0429190060a0788c0230151a47435248086e14000c806004980012037e2603c050381010011a978040100000c03a0388c0e461502408295081442751882c1a0000038001c00000240503018180003014000d098080233
  | 8=>0x20e334d381e85e0400d6900336c4f00e1846c1e225571d8f3650040e03b0143103c0112c380e421004c3088010408f0104101c02228630140e03c0f00c2b18c01018020f002008e13181403001164360218b004672203d074b7000000904100c3117008118960500812827084700004a000b30d4020ac01000b606003004170041a01c0810c5c00827034690d80d04c1206c000100700431038000182b02801040000640515c37008013400f0180102c330140d02c0000816078000100b000ad000000000102c20010040004800016
  | 9=>0xd16e05d801451001402c9040
  | _=>0
def q16 (s : Nat) (zs : List Nat) : Nat :=
  match s with
  | 6 =>
    let h:=sg 11 zs % 1048573
    let d:=(q17 6>>>(5*(h % 7)))&&&31
    let slot:=((h*1001) % 1048573+d) % 29
    (q18 6>>>(7*slot))&&&127
  | 7 =>
    let h:=sg 0 zs % 1048573
    let d:=(q17 7>>>(9*(h % 110)))&&&511
    let slot:=((h*17) % 1048573+d) % 463
    (q18 7>>>(11*slot))&&&2047
  | 8 =>
    let h:=sg 1 zs % 1048573
    let d:=(q17 8>>>(10*(h % 166)))&&&1023
    let slot:=((h*1) % 1048573+d) % 695
    (q18 8>>>(11*slot))&&&2047
  | 9 =>
    let h:=sg 13 zs % 1048573
    let d:=(q17 9>>>(6*(h % 16)))&&&63
    let slot:=((h*31) % 1048573+d) % 71
    (q18 9>>>(7*slot))&&&127
  | _=>0
def yd (g : Nat) (ws : List Nat) :=
  if g=0 then ws else if g=1 then q38 ws else if g=2 then q37 ws else q38 (q37 ws)
lemma q0v (g : Nat) {s ws} (h : NatRun q7 qe s ws) :
    NatRun q7 qe s (yd g ws):= by
  unfold yd;split
  · exact h
  · split
    · exact q3j h
    · split
      · exact q3i h
      · exact q3j (q3i h)
def qh : Nat->Nat->Bool
  | 0,i=>!(vj 0 i==[qe])
  | s+1,i =>
    let ws:=vj (s+1) i
    !(vy s ws fun tight zs =>
      !(tight&&q0x zs) &&
      (let v:=q16 s zs;!(v/4<q25 s&&(yd (v %4) zs).isPerm (vj s (v/4)))))
lemma zc {s i} (hb : qh s i=true)
    (h : NatRun q7 qe s (vj s i)) :
    ∃ q<s,∃ j<q25 q,NatRun q7 qe q (vj q j):= by
  cases s with
  | zero=>simp [qh,q1f h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tight : Bool) (zs : List Nat):=!(tight&&q0x zs) &&
      (let v:=q16 s zs;!(v/4<q25 s&&(yd (v %4) zs).isPerm (vj s (v/4))))
    have hF (zs) (hz : NatRun q7 qe s zs) : F (decide (zs.length=s+1)) zs=true:= by
      simp only [F,Bool.and_eq_true,Bool.not_eq_true']
      constructor
      · by_cases hl : zs.length=s+1
        · simp [hl,q1n hz hl]
        · simp [hl]
      · simp only [Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj;by_contra! hp
        have p:=List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (q0v _ hz))
    have hN:=y0 h s rfl _ (List.Perm.refl _) F hF
    change !(vy _ _ F)=true at hb;rw [hN] at hb;contradiction
lemma q0k {cap : Nat}
    (hc : ∀ s ≤ cap,∀ i<q25 s,qh s i=true) :
    ∀ s ≤ cap,∀ i<q25 s,¬ NatRun q7 qe s (vj s i):= by
  intro s;induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩:=zc (hc s hs i hi) hh
    exact ih q hq (by omega) j hj h
set_option maxHeartbeats 0 in
lemma q3h :
    qh 0 0=true/\qh 1 0=true/\qh 2 0=true ∧
    qh 3 0=true/\qh 4 0=true/\qh 5 0=true:= by decide +kernel
set_option maxHeartbeats 0 in
lemma z6 : span (qh 6) 19 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3s : span (qh 7) 100 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3r : span (qh 7) 100 100=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3q : span (qh 7) 92 200=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3p : span (qh 8) 100 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3o : span (qh 8) 100 100=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3n : span (qh 8) 100 200=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3m : span (qh 8) 65 300=true:= by decide +kernel
set_option maxHeartbeats 0 in
lemma z9 : span (qh 9) 26 0=true:= by decide +kernel
set_option maxHeartbeats 0 in
lemma q3z : span (qh 10) 1 0=true:= by decide +kernel
lemma z7 : span (qh 7) 292 0=true:=(@span_join (qh 7) 100 0 192 q3s (@span_join (qh 7) 100 100 92 q3r q3q))
lemma z8 : span (qh 8) 365 0=true:=(@span_join (qh 8) 200 0 165 (@span_join (qh 8) 100 0 100 q3p q3o) (@span_join (qh 8) 100 200 65 q3n q3m))
lemma q2x (s : Nat) (hs : s ≤ 10) : ∀ i<q25 s,qh s i=true:= by
  interval_cases s
  · intro i hi;simp only [q25] at hi;have h0 : i=0:=(by omega);subst h0;exact q3h.1
  · intro i hi;simp only [q25] at hi;have h0 : i=0:=(by omega);subst h0;exact q3h.2.1
  · intro i hi;simp only [q25] at hi;have h0 : i=0:=(by omega);subst h0;exact q3h.2.2.1
  · intro i hi;simp only [q25] at hi;have h0 : i=0:=(by omega);subst h0;exact q3h.2.2.2.1
  · intro i hi;simp only [q25] at hi;have h0 : i=0:=(by omega);subst h0;exact q3h.2.2.2.2.1
  · intro i hi;simp only [q25] at hi;have h0 : i=0:=(by omega);subst h0;exact q3h.2.2.2.2.2
  · exact fun i hi=>span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z8 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok z9 i (Nat.zero_le i) hi
  · exact fun i hi=>span_ok q3z i (Nat.zero_le i) hi
theorem GG (s : Nat) (hs : s ≤ 10) (h : NatRun (mask 232) (goal 232) s xs517) : False:= by
  rw [← vb,← vc] at h
  have h10 : NatRun q7 qe 10 xs517:=q10 h hs
  have p : xs517.Perm (vj 10 0):= by decide +kernel
  exact q0k q2x 10 (by decide) 0 (by decide) (Run.perm p h10)
theorem noSub {s : Nat} {ws : List Nat} (hs : s ≤ 10) (hsub : ws.Sublist xs517)
    (h : NatRun (mask 232) (goal 232) s ws) : False:= by
  by_cases eq : ws=xs517
  · subst ws;exact GG _ hs h
  · rw [← vb,← vc] at h
    exact yn _ (List.mem_sublists.2 hsub) eq (vl h)

def MarkedRun {α : Type} (inv : α → α) (meet join : α → α → α) (y : α)
    (s : Nat) (mark : Bool) (ws : List α) : Prop :=
  ∀ (P : Nat → Bool → List α → Prop), P 0 false [y] →
    (∀ {s : Nat} {m : Bool} {xs ys : List α}, xs.Perm ys → P s m xs → P s m ys) →
    (∀ {s : Nat} {m : Bool} {a : α} {r : List α} (neg save : Bool),
      P s m ((if neg then inv a else a) :: kept save a r) → P (s+1) (neg || m) (a :: r)) →
    (∀ {s : Nat} {m : Bool} {a b : α} {r : List α} (conj ka kb : Bool),
      P s m ((if conj then meet a b else join a b) :: kept ka a (kept kb b r)) →
        P (s+1) m (a :: b :: r)) → P s mark ws

theorem MarkedRun.done {α : Type} {inv : α → α} {meet join : α → α → α} {y : α} :
    MarkedRun inv meet join y 0 false [y] := by
  intro P hd _ _ _
  exact hd

theorem MarkedRun.perm {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}
    {s m xs ys} (p : List.Perm xs ys) (h : MarkedRun inv meet join y s m xs) :
    MarkedRun inv meet join y s m ys := by
  intro P hd hp ho ht
  exact hp p (h P hd @hp @ho @ht)

theorem MarkedRun.one {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}
    {s m a r} (neg save : Bool)
    (h : MarkedRun inv meet join y s m ((if neg then inv a else a) :: kept save a r)) :
    MarkedRun inv meet join y (s+1) (neg || m) (a :: r) := by
  intro P hd hp ho ht
  exact ho neg save (h P hd @hp @ho @ht)

theorem MarkedRun.two {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}
    {s m a b r} (conj ka kb : Bool)
    (h : MarkedRun inv meet join y s m ((if conj then meet a b else join a b) :: kept ka a (kept kb b r))) :
    MarkedRun inv meet join y (s+1) m (a :: b :: r) := by
  intro P hd hp ho ht
  exact ht conj ka kb (h P hd @hp @ho @ht)

theorem MarkedRun.elimInd {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}
    {P : Nat → Bool → List α → Prop} (hd : P 0 false [y])
    (hp : ∀ {s m xs ys}, xs.Perm ys → MarkedRun inv meet join y s m xs → P s m xs → P s m ys)
    (ho : ∀ {s m a r} (neg save : Bool),
      let ws := (if neg then inv a else a) :: kept save a r
      MarkedRun inv meet join y s m ws → P s m ws → P (s+1) (neg || m) (a :: r))
    (ht : ∀ {s m a b r} (conj ka kb : Bool),
      let ws := (if conj then meet a b else join a b) :: kept ka a (kept kb b r)
      MarkedRun inv meet join y s m ws → P s m ws → P (s+1) m (a :: b :: r))
    {s m ws} (h : MarkedRun inv meet join y s m ws) : P s m ws := by
  apply And.right (a := MarkedRun inv meet join y s m ws)
  refine h (fun k n xs => MarkedRun inv meet join y k n xs ∧ P k n xs) ⟨MarkedRun.done,hd⟩ ?_ ?_ ?_
  · intro k n xs ys p ih
    exact ⟨MarkedRun.perm p ih.1,hp p ih.1 ih.2⟩
  · intro k n a r neg save ih
    exact ⟨MarkedRun.one neg save ih.1,ho neg save ih.1 ih.2⟩
  · intro k n a b r conj ka kb ih
    exact ⟨MarkedRun.two conj ka kb ih.1,ht conj ka kb ih.1 ih.2⟩

theorem MarkedRun.forget {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}
    {s m ws} (h : MarkedRun inv meet join y s m ws) : Run inv meet join y s ws :=
  h (fun s _ ws => Run inv meet join y s ws) Run.done
    (fun p ih => Run.perm p ih) (fun neg save ih => Run.one neg save ih)
    (fun conj ka kb ih => Run.two conj ka kb ih)

theorem MarkedRun.zero {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}
    {s m ws} (h : MarkedRun inv meet join y s m ws) : s = 0 → m = false ∧ ws = [y] := by
  apply MarkedRun.elimInd (h := h)
  · simp
  · intro s m xs ys p _ ih hs
    obtain ⟨hm,rfl⟩ := ih hs
    exact ⟨hm,List.perm_singleton.1 p.symm⟩
  · simp
  · simp

theorem MarkedRun.tight {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}
    {s m ws} (h : MarkedRun inv meet join y s m ws) : ws.length = s+1 → m = false := by
  apply MarkedRun.elimInd (h := h)
  · simp
  · intro s m xs ys p _ ih hl
    exact ih (p.length_eq.trans hl)
  · intro s m a r neg save ws tail _ hl
    dsimp [ws] at tail
    have hb := DT (MarkedRun.forget tail)
    cases save <;> simp [kept] at hl hb <;> omega
  · intro s m a b r conj ka kb ws tail ih hl
    dsimp [ws] at tail ih
    have hb := DT (MarkedRun.forget tail)
    apply ih
    cases ka <;> cases kb <;> simp [kept] at hl hb ⊢ <;> omega

theorem MarkedRun.map {α β : Type} (f : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, f (inv a) = inv' (f a)) (hm : ∀ a b, f (meet a b) = meet' (f a) (f b))
    (hj : ∀ a b, f (join a b) = join' (f a) (f b)) {y : α} {s m ws}
    (h : MarkedRun inv meet join y s m ws) : MarkedRun inv' meet' join' (f y) s m (ws.map f) := by
  apply MarkedRun.elimInd (h := h)
  · exact MarkedRun.done
  · intro s m xs ys p _ ih
    exact MarkedRun.perm (p.map f) ih
  · intro s m a r neg save ws _ ih
    dsimp [ws] at ih
    have he : ((if neg then inv a else a) :: kept save a r).map f =
        (if neg then inv' (f a) else f a) :: kept save (f a) (r.map f) := by
      cases neg <;> simp [Fd,hi]
    rw [he] at ih
    exact MarkedRun.one neg save ih
  · intro s m a b r conj ka kb ws _ ih
    dsimp [ws] at ih
    have he : ((if conj then meet a b else join a b) :: kept ka a (kept kb b r)).map f =
        (if conj then meet' (f a) (f b) else join' (f a) (f b)) ::
          kept ka (f a) (kept kb (f b) (r.map f)) := by
      cases conj <;> simp [Fd,hm,hj]
    rw [he] at ih
    exact MarkedRun.two conj ka kb ih

abbrev MarkedNatRun := MarkedRun (· ^^^ q7) (· &&& ·) (· ||| ·) qe

theorem markedMove {s m ws} (h : MarkedNatRun s m ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : r2 tag d q7 = q7) (hy : r2 tag d qe = qe) :
    MarkedNatRun s m (ws.map (r2 tag d)) := by
  unfold MarkedNatRun
  rw [← hy]
  exact MarkedRun.map _ (fun a => (yw tag d hz a q7).2.2.trans (by rw [hm]))
    (fun a b => (yw tag d hz a b).1) (fun a b => (yw tag d hz a b).2.1) h

theorem markedOrient (g : Nat) {s m ws} (h : MarkedNatRun s m ws) : MarkedNatRun s m (yd g ws) := by
  have ha : ∀ {xs}, MarkedNatRun s m xs → MarkedNatRun s m (q38 xs) :=
    fun hn => markedMove hn _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hb : ∀ {xs}, MarkedNatRun s m xs → MarkedNatRun s m (q37 xs) :=
    fun hn => markedMove hn _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  unfold yd
  split
  · exact h
  · split
    · exact ha h
    · split
      · exact hb h
      · exact ha (hb h)

theorem markedMonotonePair {s m ws} (h : MarkedNatRun s m ws) :
    m = false → ∀ i j, (∀ w ∈ ws, w.testBit i ≤ w.testBit j) → qe.testBit i ≤ qe.testBit j := by
  apply MarkedRun.elimInd (h := h)
  · intro _ i j hw
    exact hw _ (by simp)
  · intro s m xs ys p _ ih hm i j hw
    exact ih hm i j (fun w hw' => hw w (p.mem_iff.1 hw'))
  · intro s m a r neg save ws tail ih hm i j hw
    have hneg : neg = false := by cases neg <;> simp_all
    have hmark : m = false := by simpa [hneg] using hm
    have ha := hw a (by simp)
    refine ih hmark i j ?_
    intro w hw'
    dsimp [ws] at hw'
    cases save <;> simp_all [kept] <;> grind
  · intro s m a b r conj ka kb ws tail ih hm i j hw
    have ha := hw a (by simp)
    have hb := hw b (by simp)
    refine ih hm i j ?_
    intro w hw'
    dsimp [ws] at hw'
    cases conj <;> cases ka <;> cases kb <;>
      simp only [kept,Bool.false_eq_true,ite_false,ite_true,List.mem_cons] at hw' <;>
      rcases hw' with rfl | ht <;>
      first | simp only [Nat.testBit_or,Nat.testBit_and]; grind | apply hw; simp only [List.mem_cons]; tauto

theorem markedMonotoneCover {s ws} (h : MarkedNatRun s false ws) : rd ws &&& se = se := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and,yx,u4]
  by_cases hi : i < 232
  · have hy : ¬ qe.testBit (232+i) ≤ qe.testBit i := by
      rw [vc, xo, xo]
      simp [hi,show ¬ 232 ≤ i by omega]
    have hc : (rd ws).testBit i = true := by
      apply (zu i hi ws).2
      by_contra! hw
      apply hy
      apply markedMonotonePair h rfl
      intro w hw'
      specialize hw w hw'
      cases hx : w.testBit i <;> cases hz : w.testBit (232+i) <;> simp_all
    simp [hc,hi]
  · simp [hi]

def thetaClip (w : Nat) : Nat := w &&& q7

lemma thetaClip_not (a : Nat) : thetaClip (a ^^^ q7) = thetaClip a ^^^ q7 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [thetaClip, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases q7.testBit i <;> rfl

lemma thetaClip_and (a b : Nat) : thetaClip (a &&& b) = thetaClip a &&& thetaClip b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [thetaClip, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> cases q7.testBit i <;> rfl

lemma thetaClip_or (a b : Nat) : thetaClip (a ||| b) = thetaClip a ||| thetaClip b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [thetaClip, Nat.testBit_and, Nat.testBit_or]
  cases a.testBit i <;> cases b.testBit i <;> cases q7.testBit i <;> rfl

lemma thetaFlip_and (a b : Nat) :
    thetaClip (a &&& b) ^^^ q7 = (thetaClip a ^^^ q7) ||| (thetaClip b ^^^ q7) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [thetaClip, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases q7.testBit i <;> rfl

lemma thetaFlip_or (a b : Nat) :
    thetaClip (a ||| b) ^^^ q7 = (thetaClip a ^^^ q7) &&& (thetaClip b ^^^ q7) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [thetaClip, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases q7.testBit i <;> rfl

lemma thetaClipRun {s ws} (h : NatRun q7 qe s ws) : NatRun q7 qe s (ws.map thetaClip) := by
  have hg : thetaClip qe = qe := by decide +kernel
  nth_rw 1 [← hg]
  exact Run.map thetaClip thetaClip_not thetaClip_and thetaClip_or h

def thetaOrientLeaf (w v : Nat) : Prop := v = thetaClip w ∨ v = thetaClip w ^^^ q7

lemma thetaOrientIdentity (ws : List Nat) : List.Forall₂ thetaOrientLeaf ws (ws.map thetaClip) := by
  induction ws with
  | nil => exact .nil
  | cons w ws ih => exact .cons (Or.inl rfl) ih

theorem thetaOrientedTight {s ws} (h : MarkedNatRun s true ws) (hlen : ws.length = s) :
    ∃ vs, List.Forall₂ thetaOrientLeaf ws vs ∧ NatRun q7 qe (s - 1) vs := by
  let P : Nat → Bool → List Nat → Prop := fun s mark ws => mark = true → ws.length = s →
    ∃ vs, List.Forall₂ thetaOrientLeaf ws vs ∧ NatRun q7 qe (s - 1) vs
  refine MarkedRun.elimInd (P := P) ?_ ?_ ?_ ?_ h rfl hlen
  · simp [P]
  · intro s m xs ys p _ ih hm hl
    obtain ⟨vs, hv, ht⟩ := ih hm (p.length_eq.trans hl)
    obtain ⟨zs, hz, hperm⟩ := List.perm_comp_forall₂ p.symm hv
    exact ⟨zs, hz, Run.perm hperm.symm ht⟩
  · intro s m a r neg save old tail _ hm hl
    have hv := DT (MarkedRun.forget tail)
    have hr : r.length = s := by simpa [P] using hl
    have hsave : save = false := by
      cases save <;> simp [old, kept, hr] at hv ⊢
    subst save
    have hs : old.length = s + 1 := by simp [old, kept, hr]
    have hfalse := MarkedRun.tight tail hs
    cases neg
    · simp [hfalse] at hm
    · refine ⟨thetaClip (a ^^^ q7) :: r.map thetaClip, ?_, ?_⟩
      · exact .cons (Or.inr (thetaClip_not a)) (thetaOrientIdentity r)
      · have hrun := thetaClipRun (MarkedRun.forget tail)
        simpa [old, kept] using hrun
  · intro s m a b r conj ka kb old tail ih hm hl
    have hlr : r.length + 1 = s := by
      change r.length + 1 + 1 = s + 1 at hl
      omega
    have hv := DT (MarkedRun.forget tail)
    have hnon : old.length ≠ s + 1 := fun he => Bool.false_ne_true ((MarkedRun.tight tail he).symm.trans hm)
    have hv' : old.length ≤ s := by omega
    have hk : ka = false ∧ kb = false := by
      cases ka <;> cases kb <;> simp [old, kept] at hv' ⊢ <;> omega
    rcases hk with ⟨rfl, rfl⟩
    have hn : old.length = s := by simpa [old, kept] using hlr
    obtain ⟨vs, hv, hrun⟩ := ih hm hn
    change List.Forall₂ thetaOrientLeaf ((if conj then a &&& b else a ||| b) :: r) vs at hv
    cases hv with
    | @cons _ c _ rest hhead hrest =>
      have hs : s - 1 + 1 = s := by omega
      rcases hhead with hp | hp
      · refine ⟨thetaClip a :: thetaClip b :: rest, ?_, ?_⟩
        · exact .cons (Or.inl rfl) (.cons (Or.inl rfl) hrest)
        · have hc : c = if conj then thetaClip a &&& thetaClip b else thetaClip a ||| thetaClip b := by
            cases conj <;> simpa [thetaOrientLeaf, thetaClip_and, thetaClip_or] using hp
          rw [hc] at hrun
          have hstep := Run.two conj false false hrun
          simpa [kept, hs] using hstep
      · refine ⟨(thetaClip a ^^^ q7) :: (thetaClip b ^^^ q7) :: rest, ?_, ?_⟩
        · exact .cons (Or.inr rfl) (.cons (Or.inr rfl) hrest)
        · have hc : c = if !conj then (thetaClip a ^^^ q7) &&& (thetaClip b ^^^ q7)
            else (thetaClip a ^^^ q7) ||| (thetaClip b ^^^ q7) := by
            cases conj <;> simpa [thetaOrientLeaf, thetaFlip_and, thetaFlip_or] using hp
          rw [hc] at hrun
          have hstep := Run.two (!conj) false false hrun
          simpa [kept, hs] using hstep

def thetaPairCover (coverage : Nat) : Bool := coverage &&& se == se

private theorem thetaMaskBit (i : Nat) : se.testBit i = decide (i < 232) := by
  rw [yx, u4]

private theorem thetaPairCover_bits {coverage : Nat} :
    thetaPairCover coverage = true ↔ ∀ i < 232, coverage.testBit i = true := by
  unfold thetaPairCover
  rw [beq_iff_eq]
  constructor
  · intro h i hi
    have hb := congrArg (fun n : Nat => n.testBit i) h
    simpa only [Nat.testBit_and, thetaMaskBit, hi, decide_true, Bool.and_true] using hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, thetaMaskBit]
    by_cases hi : i < 232
    · simp [hi, h i hi]
    · simp [hi]

private theorem thetaClip_bits (w i : Nat) (hi : i < 464) :
    (thetaClip w).testBit i = w.testBit i := by
  simp only [thetaClip, Nat.testBit_and, vb, zn]
  have he : i < 232 + 232 := by omega
  simp [he]

private theorem thetaOrient_diff {w v i : Nat} (hi : i < 232) (ha : thetaOrientLeaf w v)
    (h0 : v.testBit i = false) (h1 : v.testBit (232 + i) = true) :
    (vd w).testBit i = true := by
  have hb : i < 464 := by omega
  have hc : 232 + i < 464 := by omega
  simp only [vd, Nat.testBit_xor, Nat.testBit_shiftRight]
  rcases ha with h | h
  · rw [h, thetaClip_bits _ _ hb] at h0
    rw [h, thetaClip_bits _ _ hc] at h1
    simp [h0, h1]
  · rw [h, Nat.testBit_xor, thetaClip_bits _ _ hb, vb, zn] at h0
    rw [h, Nat.testBit_xor, thetaClip_bits _ _ hc, vb, zn] at h1
    have hd : i < 232 + 232 := by omega
    have he : 232 + i < 232 + 232 := by omega
    simp [hd] at h0
    simp [he] at h1
    cases hp : w.testBit i <;> cases hn : w.testBit (232 + i) <;> simp_all

private theorem thetaDirectedOfSigns {ws vs : List Nat} (hrel : List.Forall₂ thetaOrientLeaf ws vs)
    (i : Nat) (hi : i < 232) :
    (rd vs).testBit i = true → (s9 ws).testBit i = true := by
  induction hrel with
  | nil => simp [rd]
  | cons h hs ih =>
    simp only [rd, s9, Nat.testBit_or, Bool.or_eq_true]
    intro hstep
    rcases hstep with hp | hp
    · left
      simp only [sq, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_xor, thetaMaskBit,
        hi, decide_true, Bool.and_eq_true, Bool.xor_true] at hp
      exact thetaOrient_diff hi h (by simpa using hp.2) hp.1
    · exact Or.inr (ih hp)

private theorem thetaRdAppend (xs ys : List Nat) :
    rd (xs ++ ys) = rd xs ||| rd ys := by
  induction xs with
  | nil => simp [rd]
  | cons x xs ih => simp [rd, ih, Nat.or_assoc]

-- Try a polarity for each wire, discarding a choice if the remaining wires cannot
-- separate all opposite-labelled row pairs. Test the six-row potentials at the leaves.
def thetaOrientationPossible : List Nat → List Nat → Bool
  | [], chosen => thetaPairCover (rd chosen) && !q0x chosen
  | w :: ws, chosen =>
    thetaPairCover (rd chosen ||| s9 (w :: ws)) &&
      (thetaOrientationPossible ws (thetaClip w :: chosen) ||
       thetaOrientationPossible ws ((thetaClip w ^^^ q7) :: chosen))

private theorem thetaOrientationSound {ws vs : List Nat} (hrel : List.Forall₂ thetaOrientLeaf ws vs)
    (s : Nat) (chosen : List Nat) (h : NatRun q7 qe s (vs ++ chosen))
    (hsize : (vs ++ chosen).length = s + 1) :
    thetaOrientationPossible ws chosen = true := by
  induction hrel generalizing chosen with
  | nil =>
    simp only [List.nil_append] at h hsize
    simp only [thetaOrientationPossible, thetaPairCover, rl h hsize, beq_self_eq_true,
      q1n h hsize, Bool.not_false, Bool.and_self]
  | @cons w v ws vs hv hrel ih =>
    have hcover : thetaPairCover (rd chosen ||| s9 (w :: ws)) = true := by
      apply thetaPairCover_bits.mpr
      intro i hi
      have hbits := thetaPairCover_bits.mp (show thetaPairCover (rd ((v :: vs) ++ chosen)) = true by
        rw [thetaPairCover, rl h hsize]; simp) i hi
      rw [thetaRdAppend, Nat.testBit_or, Bool.or_eq_true] at hbits
      rw [Nat.testBit_or, Bool.or_eq_true]
      exact hbits.elim (fun p => Or.inr (thetaDirectedOfSigns (.cons hv hrel) i hi p)) Or.inl
    have hp : ((v :: vs) ++ chosen).Perm (vs ++ v :: chosen) := List.perm_middle.symm
    have hi := ih (v :: chosen) (Run.perm hp h) (hp.length_eq.symm.trans hsize)
    simp only [thetaOrientationPossible, Bool.and_eq_true, Bool.or_eq_true]
    exact ⟨hcover, hv.elim (fun e => Or.inl (e ▸ hi)) (fun e => Or.inr (e ▸ hi))⟩

def thetaOneNotImpossible (ws : List Nat) : Bool := !thetaOrientationPossible ws []

lemma thetaOneNotImpossibleSound {s ws} (h : MarkedNatRun s true ws)
    (hlen : ws.length = s) (hs : 0 < s) : thetaOneNotImpossible ws = false := by
  obtain ⟨vs, hv, hr⟩ := thetaOrientedTight h hlen
  have hlen' : (vs ++ []).length = (s - 1) + 1 := by
    rw [List.append_nil, ← hv.length_eq, hlen]
    omega
  have hr' : NatRun q7 qe (s - 1) (vs ++ []) := by simpa only [List.append_nil] using hr
  simp [thetaOneNotImpossible, thetaOrientationSound hv (s - 1) [] hr' hlen']

lemma thetaOneNotImpossible_false {k zs} (h : MarkedNatRun k true zs) (hlen : zs.length = k) :
    thetaOneNotImpossible zs = false := by
  have hk : 0 < k := by
    by_contra! hn
    obtain ⟨ht,_⟩ := MarkedRun.zero h (by omega)
    contradiction
  exact thetaOneNotImpossibleSound h hlen hk

def thetaAnn : List Nat → List (Nat × Nat × Nat × Nat × Nat)
  | [] => []
  | w :: ws =>
    let p := thetaClip w
    let n := p ^^^ q7
    (p, n, sq p, sq n, s9 (w :: ws)) :: thetaAnn ws

def thetaFastOrient : List (Nat × Nat × Nat × Nat × Nat) → Nat → List Nat → Bool
  | [], coverage, chosen => thetaPairCover coverage && !q0x chosen
  | (p,n,dp,dn,available) :: ws, coverage, chosen =>
    thetaPairCover (coverage ||| available) &&
      (thetaFastOrient ws (dp ||| coverage) (p :: chosen) ||
       thetaFastOrient ws (dn ||| coverage) (n :: chosen))

lemma thetaFastOrient_eq (ws chosen : List Nat) :
    thetaFastOrient (thetaAnn ws) (rd chosen) chosen = thetaOrientationPossible ws chosen := by
  induction ws generalizing chosen with
  | nil => rfl
  | cons w ws ih =>
    change (thetaPairCover (rd chosen ||| s9 (w :: ws)) &&
      (thetaFastOrient (thetaAnn ws) (rd (thetaClip w :: chosen)) (thetaClip w :: chosen) ||
        thetaFastOrient (thetaAnn ws) (rd ((thetaClip w ^^^ q7) :: chosen))
          ((thetaClip w ^^^ q7) :: chosen))) = _
    rw [ih, ih] <;> rfl

def thetaOneNotFast (ws : List Nat) : Bool := !thetaFastOrient (thetaAnn ws) 0 []

lemma thetaOneNotFast_false {k ws} (h : MarkedNatRun k true ws) (hlen : ws.length = k) :
    thetaOneNotFast ws = false := by
  change (!thetaFastOrient (thetaAnn ws) (rd []) []) = false
  rw [thetaFastOrient_eq]
  exact thetaOneNotImpossible_false h hlen

def vyMarked (s : Nat) (ws : List Nat) (f : Bool->Bool->List Nat->Bool) : Bool :=
  let len:=ws.length
  let slack:=s+2 - len
  let t0:=decide (len=s+2)
  let t1:=decide (len=s+1)
  let t2:=decide (len=s)
  ws.any fun a =>
    let ra:=ws.erase a
    let da:=vd a
    let dau:=sq a
    (slack ≥ 1 &&
      (let cra:=if t1&&slack==1 then 0 else s9 ra
       let crau:=if t1||t2 then rd ra else 0
       [false,true].any fun neg =>
        let w:=if neg then a^^^q7 else a
        (((if t1 then sq w|||crau else vd w|||cra)&&&se==se)&&f neg t1 (w :: ra)) ||
        (slack ≥ 2 &&
          ((if t2 then sq w|||(dau|||crau) else vd w|||(da|||cra))&&&se==se) &&
          f neg t2 (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b &&
      (let r:=ra.erase b
       let db:=vd b
       let dbu:=sq b
       let cr:=if t0 then 0 else s9 r
       let cru:=if t0||t1||t2 then rd r else 0
       [false,true].any fun conj =>
        let w:=if conj then a&&&b else a|||b
        let dw:=if t0 then 0 else vd w
        let dwu:=if t0||t1||t2 then sq w else 0
        (((if t0 then dwu|||cru else dw|||cr)&&&se==se)&&f false t0 (w :: r)) ||
        (slack ≥ 1 &&
          ((((if t1 then dwu|||(dau|||cru) else dw|||(da|||cr))&&&se==se)&&f false t1 (w :: a :: r)) ||
           (((if t1 then dwu|||(dbu|||cru) else dw|||(db|||cr))&&&se==se)&&f false t1 (w :: b :: r)))) ||
        (slack ≥ 2 &&
          ((if t2 then dwu|||(dau|||(dbu|||cru)) else dw|||(da|||(db|||cr)))&&&se==se) &&
          f false t2 (w :: a :: b :: r)))
lemma markedUnary {a rest} {neg save : Bool} {s m ws} (p : (a :: rest).Perm ws)
    (h : MarkedNatRun s m ((if neg then a^^^q7 else a) :: kept save a rest))
    (f : Bool->Bool->List Nat->Bool) (hf : ∀ ys,MarkedNatRun s m ys->f neg (decide (ys.length=s+1)) ys=true) :
    vyMarked s ws f=true:= by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a):=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hh:=DT (MarkedRun.forget h);have hl:=p.length_eq;simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length:= by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩;rw [Bool.or_eq_true];left
  rw [Bool.and_eq_true];refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have hrm:=MarkedRun.perm ((y1 pr save a).cons _) h
  have ht:=hf _ hrm
  have hrun:=MarkedRun.forget hrm
  have hcov:=vl hrun
  cases save with
  | false =>
    simp only [kept,Bool.false_eq_true,ite_false] at ht hrun hcov
    have hlen : ((if neg then a^^^q7 else a) :: ws.erase a).length=ws.length:= by
      simp [List.length_erase_of_mem ha];omega
    rw [hlen] at ht
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,Bool.true_or,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h1,decide_false,Bool.false_and,s9] at ht hcov ⊢
      simp [hcov,ht]
  | true =>
    simp only [kept,ite_true] at ht hrun hcov
    simp only [kept,ite_true,List.length_cons] at hh
    have hsl2 : 2 ≤ s+2-ws.length:= by omega
    have hlen : ((if neg then a^^^q7 else a) :: a :: ws.erase a).length=ws.length+1:= by
      simp [List.length_erase_of_mem ha];omega
    have hlen_eq : decide (((if neg then a^^^q7 else a) :: a :: ws.erase a).length=s+1)=decide (ws.length=s):= by
      rw [hlen];exact decide_eq_decide.mpr (by omega)
    rw [hlen_eq] at ht
    by_cases h2 : ws.length=s
    · have hcu:=rl hrun (by omega)
      simp only [h2,decide_true,Bool.or_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · have h1 : ws.length ≠ s+1:= by omega
      simp only [h1,h2,decide_false,Bool.false_and,s9] at ht hcov ⊢
      simp [decide_eq_true hsl2,hcov,ht]
lemma markedBinaryOrdered {a b rest} {conj ka kb : Bool} {s m ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : MarkedNatRun s m ((if conj then a&&&b else a|||b) :: kept ka a (kept kb b rest)))
    (f : Bool->Bool->List Nat->Bool) (hf : ∀ ys,MarkedNatRun s m ys->f false (decide (ys.length=s+1)) ys=true) :
    vyMarked s ws f=true:= by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pp:=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hb:=pp.mem_iff.1 List.mem_cons_self
  have pr:=(pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh:=DT (MarkedRun.forget h);have hl:=p.length_eq;simp only [List.length_cons] at hl hh
  have hlenr : ((ws.erase a).erase b).length=ws.length - 2:= by
    have:=pr.length_eq;omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩;rw [Bool.or_eq_true];right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩;rw [Bool.and_eq_true];refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have hrm:=MarkedRun.perm ((y1 (y1 pr kb b) ka a).cons _) h
  have ht:=hf _ hrm
  have hrun:=MarkedRun.forget hrm
  have hcov:=vl hrun
  cases ka <;> cases kb
  · simp only [kept,Bool.false_eq_true,ite_false] at ht hh hrun hcov
    have hlen : ((if conj then a&&&b else a|||b) :: (ws.erase a).erase b).length=ws.length - 1:= by
      simp [hlenr];omega
    have hle : decide (((if conj then a&&&b else a|||b) :: (ws.erase a).erase b).length=s+1)=decide (ws.length=s+2):= by
      rw [hlen];exact decide_eq_decide.mpr (by omega)
    rw [hle] at ht
    by_cases h0 : ws.length=s+2
    · have hcu:=rl hrun (by omega)
      simp only [h0,decide_true,Bool.true_or,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,decide_false,s9] at ht hcov ⊢
      simp [hcov,ht]
  · simp only [kept,Bool.false_eq_true,ite_false,ite_true] at ht hrun hcov
    simp only [kept,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at hh
    have hsl1 : 1 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: b :: (ws.erase a).erase b).length=ws.length:= by
      simp [hlenr];omega
    rw [hlen] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h1,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl1,hcov,ht]
  · simp only [kept,Bool.false_eq_true,ite_false,ite_true] at ht hrun hcov
    simp only [kept,Bool.false_eq_true,ite_false,ite_true,List.length_cons] at hh
    have hsl1 : 1 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: a :: (ws.erase a).erase b).length=ws.length:= by
      simp [hlenr];omega
    rw [hlen] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h1 : ws.length=s+1
    · have hcu:=rl hrun (by omega)
      simp only [h1,decide_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h1,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl1,hcov,ht]
  · simp only [kept,ite_true] at ht hrun hcov
    simp only [kept,ite_true,List.length_cons] at hh
    have hsl2 : 2 ≤ s+2 - ws.length:= by omega
    have hlen : ((if conj then a&&&b else a|||b) :: a :: b :: (ws.erase a).erase b).length=ws.length+1:= by
      simp [hlenr];omega
    have hle : decide (((if conj then a&&&b else a|||b) :: a :: b :: (ws.erase a).erase b).length=s+1)=decide (ws.length=s):= by
      rw [hlen];exact decide_eq_decide.mpr (by omega)
    rw [hle] at ht
    have h0 : ws.length ≠ s+2:= by omega
    by_cases h2 : ws.length=s
    · have hcu:=rl hrun (by omega)
      simp only [h2,decide_true,Bool.or_true,ite_true,rd] at ht hcu ⊢
      simp [hcu,ht]
    · simp only [h0,h2,decide_false,s9] at ht hcov ⊢
      simp [decide_eq_true hsl2,hcov,ht]
lemma markedBinary {a b rest} {conj ka kb : Bool} {s m ws}
    (p : (a :: b :: rest).Perm ws)
    (h : MarkedNatRun s m ((if conj then a&&&b else a|||b) :: kept ka a (kept kb b rest)))
    (f : Bool->Bool->List Nat->Bool) (hf : ∀ ys,MarkedNatRun s m ys->f false (decide (ys.length=s+1)) ys=true) :
    vyMarked s ws f=true:= by
  rcases le_total a b with hab | hba
  · exact markedBinaryOrdered hab p h f hf
  · apply markedBinaryOrdered (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a&&&b else a|||b)=(if conj then b&&&a else b|||a):= by
      cases conj <;> simp [Nat.and_comm,Nat.or_comm]
    rw [he] at h;apply MarkedRun.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept];exact List.Perm.swap _ _ _

lemma markedStep {s m ws} (h : MarkedNatRun s m ws) :
    ∀ k, s = k+1 → ∀ raw, ws.Perm raw → ∀ f : Bool → Bool → List Nat → Bool,
      (∀ neg mk xs, m = (neg || mk) → MarkedNatRun k mk xs →
        f neg (decide (xs.length = k+1)) xs = true) → vyMarked k raw f = true := by
  apply MarkedRun.elimInd (h := h)
  · simp
  · intro s m xs ys p _ ih k hk raw q f hf
    exact ih k hk raw (p.trans q) f hf
  · intro s m a r neg save ws tail _ k hk raw p f hf
    dsimp [ws] at tail
    obtain rfl : s = k := by omega
    exact markedUnary p tail f (fun xs h => hf neg m xs rfl h)
  · intro s m a b r conj ka kb ws tail _ k hk raw p f hf
    dsimp [ws] at tail
    obtain rfl : s = k := by omega
    exact markedBinary p tail f (fun xs h => hf false m xs (by simp) h)
def thetaHot : Nat → Nat
  | 0 => xs517.getD 3 0
  | 1 => xs517.getD 0 0
  | 2 => xs517.getD 5 0
  | 3 => xs517.getD 1 0
  | 4 => xs517.getD 2 0
  | 5 => xs517.getD 4 0
  | 6 => xs517.getD 6 0
  | _ => 0
def thetaRecipeBlocks : Nat → Nat → Nat
  | 0, 0 => 0x31b4801003e004002800401a001006401401a001003800c04a001016800c011003002801403e00000200000150180054010016001002403c01a016006800001400000100000100000000000018000003000001b000004c00000b000001c000017000000c00000f
  | 0, 1 => 0x63e8802000a4940064308015093005400000a001007417801900407c80090be00b00283080190050064100009009002400400d000006401000100342f8008016009004402801900200680101ee00b0064004002003004805c01101200680181f20040128250016
  | 0, 2 => 0x80058000058000006800c24d0c200446d0016004005402400d004007802c01a001002921400103900580143021b4000828401100100a42ac00d009000800c03e0001cb0024001004007400472e4950034100011016002875c0190051cb80040120030058000048
  | 0, 3 => 0x5d000004000046b000c015002005404400a454006805801606d004403000d04000340200091db00640046d200501b801072e0070064df000900007b004c01201300580280020000190000009004069801102606a005402c00901f006400906a00100a800401e
  | 0, 4 => 0x13001800003e000024001017600403a80001c00000300000130000072000005c00004200040110000940030009000026004c015011006809001602400281f40160ab004401002e0ab005403000100105e4178015494001525001100442f81c8009004000802000d
  | 0, 5 => 0x4006825000a003082801020a00401180102da050005801c016495001516800d00300a412c015495005427401505e00240081f249400042ac019093006400001600000f0000dde00003300000a400c001800008c000043000005000041a00001880090038000114
  | 0, 6 => 0x700040100090160008004016003054800c06900000d00ac016009001800037801342f8030002008094802005a01301280310be04b00140311ad00800380000e801600b802804a00a07b802872e000457000116001900a401c03e00800540010bc1d90064024019
  | 0, 7 => 0x1fd002424c0090032164ca001948c006527001931b006516c01945c00651f801904000647f40192970064c6001949200651dc01900c00649bc01943a00650d80194140064ae8019004044875c01524c00651880191d3002472c00a0001cb916c0090c2002404420a
  | 0, 8 => 0x32400551740150c200352940153140054d100152be005528401532a005526801549e005524001548e00551fc015441005519001544000549b80152ba005400c25243d00547f40051fd00450fc0152cf005523000948600252280094790024b1c00946a002521c009
  | 0, 9 => 0x33b001528c0054a200151ec00d32e003520400d335004526c01148700452100114970044bd001149f0045280011493004525401148000451e001147d00451e80114680044b800112df004519c011297003400ca8d001270529801532b00552440154430055290015
  | 0, 10 => 0x4425801108e004420801102e0041f380107c20041e980110160041e7801100e0043ff8010ff60043fc8010f8a0043e18010f720043cd8010696003430800d0ba00344b800d0220031f0800c78e003400800cf6e0011f0800473a00144891180060013e48004f8e
  | 0, 11 => 0x451005913401644c0059138016447005891c01642e00580150b6429005801509e426005887401600541890580163fd0058fec0160051e18014fd63f30058fc80160053f18014fb20053eb80146fa3de0058f740160051ad8f600163d70058014f520053d58014f4a
  | 0, 12 => 0x6300580040460db43840e401a456006914c01a447006910801a05e00040190b6233006801908a006421906401a006417801903a40700687bc01a01300142ac0011e100680187120063e78018f9a0090058018f860063e080186c244e002911400a1f40028afc016
  | 0, 13 => 0x48f03300190080014de001500901b40040a927a005402401507f00540002700024134008019095002402c1a10041f7404c1650011f7402416507d006428400927a0024008245004069401001900402740240cd00807b40280cd4090064020ddd024006800418e
  | 0, 14 => 0x3f9000409402d00341141b40190003e8035001900c00291d801900300b835801933e006400c01a00a006920801906b006427c019013006403072d099006401009e003006400122048900440000a9006412400c25501302e400cfbd00048b000123400009b09e8019
  | 0, 15 => 0x60005418401500001110dc0150003bd00150b1444005415c0150070054158015005411503c01500701241a401500047c002004900a012501001a0020ef8fb400a0021b88de00090b8002429c00942c00251d80094740024cf800907e0025090009001404403003d
  | 1, 0 => 0x40b840101f500107d40110a100540280280b10021f7902400a0690028158016006411802c16600b07b802c04a00047000011c400b05d402c0e908100b401903200a01a404c0690061f7809c01601a00b40011c80003bc00011cc0d6005520c01549d00542a0015
  | 1, 1 => 0x7033801c6a20070128000ec4000461020401d0003b4000118c01c00740e400a05500740090a200142b4001194000466109001a0003b6015c0010070ac40010a104100a42d400a01500a400d0ed01341a400d0e9003434400c1f900304f41f400a0040994011111
  | 1, 2 => 0x455002806e00a03380000a00003ab0000eb000543980282b133e000418400137d00580090de006435804c1750130ac4008222474000429c00100002101f800a00007e413c00a00106a400417500143940310bd0003af000117800045f000118000701b801c1a2
  | 1, 3 => 0x43c00010f80090104180011459004402401200407f514001100c09440300591870034000e9c099000812400205e006800112409300580280ea00044f10ec01a00b0ac80007de00b03a8fe4002424000800104640f0008fbc00200009e0de000143a00580280a6
  | 1, 4 => 0x43300102420041f783300160090298024076004074914000a0000540a1c01a0043f8802472e02b006801033245200480101fe00403180101f604b004520801106b004476c0110d400451d801100c0044010de90090338024dde0090de8000e900090254df0005
  | 1, 5 => 0x1057400c22a003454800c1fe00c025400c0d6003095800d03e00c015400c0aa0030c0800cfbe49800341ac00d09f003526400d0a700341d801a00c1d4400c76d474003435000d00346d4df800d0a8003400cde901303040240b200043100010c8000248002406a
  | 1, 6 => 0x137a80111be00142880040c600102b80041d206d00142a400549d00151d40050550084004de9000415120800500343a81d800208000080c002a00307e800c22200304f91b000500442c80102660a3006828c00a00041b000107000041d000107c0003a000110a2
  | 1, 7 => 0x1090800430e0011f780050320014378000fe8482006804c2fe0ab003875004e0003fe120800e4820048001004013025804c16601301b8000e5c01308142a00120400018001028001076800d1be00337a800103400c377803006500901c91bc01a00c01c4001040
  | 1, 8 => 0x1304292540160080198000f7c1db004925000a494000876c00246d00091bc0020003ea00202061bd000801111200105e8de40060003f00000e4448900180203720a800180200c204b0048000fd00080de80201ee0003f60000fdc026008402020500142b800437e
  | 1, 9 => 0x43800280160130038000f0c0003c50000e000003830000f1c0003c90000f280003cc004c07206d004835801a06d0068000e140a900382ac0020003d1035801600106a83580020003d60000e20498001818400e01302680980220031db8000f6800038a1254012
  | 1, 10 => 0x3ca0058014e060053808014f120053c380110420043fe8010f2a0043c78010f420043828010f160033ad800ce2e0033d9800ce220033cf800cf3a0033cb800ce0a0010da8004f164960044f000153b900551f0019466006400018c0083e880210be37b0068000038
  | 1, 11 => 0x80008020012008000402401a000015000006800002e000006c003002425001a0b60068e8401a00640d8e6001a0063d08f2801a0063c88018e02449002815000a0023cb8008f0a46e0058ea80163a700580150c63940058014fd20053ee8fa40160053d38014f46
  | 1, 12 => 0x342f40140a602c0004014dde03a00540080be00002940040b10021a8809800904200240041a10bf000400c0bd0040ac4004069055006410801501900542fc0091b4000401006900402c401004901000640040cd004033410400900402f40040490030de40040b9
  | 1, 13 => 0x2600380042b200102580040be001059800c17600303a80c000200301080c0012001025400c1a20031a8800c06e003033800c37105500340100a600101d40100ce00437780042fd04100451ac0110010164000fa20001a8800037a00003380700010010ac4054001
  | 1, 14 => 0x2c006401c6d100b1b4400125800a1b442fc01500105940182450003bf00400090090de40102450041b440041bd0011a840041ed0010de4048019005064400c1ed00102f400c03d00306840480091b400540046d1003033400c6a10031b4400c04900103a800c206
  | 1, 15 => 0xdf002437000900800f40090a900140240180ba0000dc000c02d00607b8018dde0a100640640190131cb400c0a9003027401017500400b400c0b9000081035c0193ed00641080190011cb40040150093e8404cfa1015005400d03100907c40201f101307c4005031
  | 2, 0 => 0x641a800c1750030ac475000100303a400c00100437b40041250003b90000ee800506880011b800b005802c001000055006800100001c12640150260054028015069000420401500b005402c04901301240040a5060002401c00900242840280090020ac40281a1
  | 2, 1 => 0xb500080082b20003aa01f000200b000802800a00a00050bc0160000bf0000eb40130004000074042000415400100103a400116800100040210bd01342f401c01a007002800075000142c400010400142a4004ded03a007400009437b00040011a4001424400437d
  | 2, 2 => 0x301c400c1090c200683080160c2004801006a00900280100be0041b4827c011026004404c01100446d40240050090bf40002b00dc00440242510040cc404c251008094400c2fd0030104020059013016400c331009016401c00200044a000511106a006824c00a
  | 2, 3 => 0x4060100012040006815400e0400028030066040003815403200c015803000e00c004803001a00102980040760010de8004dde00c001400420500002c000c02a003000800107800301d8024056003452800c0b200301a800c15a030005800c19200302e800c205
  | 2, 4 => 0x6d00092740020001a8125000602600c804d1ae013000800016400038b01040060001b400001f00003e50000e340003e900200ea0040ac8000e3c0940008000fb800101a800474e00002f00040420000da000428e0010128000e5001300680001a00130108000208
  | 2, 5 => 0xf100003c60000f2c0003ce02a40120003cf01b400e
  | _, _ => 0
def thetaStateGroup : Nat → Bool → Nat × Nat × Nat × Nat × Nat × Nat
  | 6, true => (0,1,0,1,0,2)
  | 7, false => (1,314,1,105,2,419)
  | 7, true => (315,20,106,7,421,27)
  | 8, false => (335,916,113,306,448,1236)
  | 8, true => (1251,131,419,44,1684,176)
  | 9, false => (1382,357,463,119,1860,478)
  | 9, true => (1739,171,582,57,2338,228)
  | 10, false => (1910,6,639,2,2566,12)
  | 10, true => (1916,20,641,7,2578,29)
  | 11, true => (1936,1,648,1,2607,2)
  | _, _ => (0,0,0,0,0,0)
def thetaShiftBlocks : Nat → Nat → Nat
  | 0, 0 => 0x403405d00c000000400c000001003a000002001c008002007000c0040000020010008003000000401600100280040000000000004006001005001c0040360048000006001001800c0020000010000000002000004400600100080080120050040000006000
  | 0, 1 => 0x10000000007000000003200500100040080000008000000000005801800000500000040080000000008000000001800000000000380180040000020000000007002800c0000010048010004003001002800c000001000000800700200000040000008000004001
  | 0, 2 => 0x1804c002003001002000400000000000100050000000000001000804003000000c802000200b002000c00600000380140020010010000012002004801400400800300040000020000000002007000800c00800f005806800c000001000400c000002800c018010
  | 0, 3 => 0xc01600d000002400400000900040040010018004000001002800401000f002800400400600380240000020028004014000002001c014004000002400200100c000c01c004000001000e0130000020012004000001001a007000800401e0010088004000000
  | 0, 4 => 0x8008008000000800c00e0010008000000000002800800600300200040000070000000000005004801c00200c000800000c013006800800000000700c8004002007003c0000050018000002000000800c00400000080000060000000008000004004000401a001
  | 0, 5 => 0x2800a0030038000000004002803c002001000800c02800900280000020010078018002001003004801600500e0000002004000000000400d0018038000001005000c00000f0048024000000001800c000000000000000600100280000060020048008004017
  | 0, 6 => 0x5005001400000000100000040000058010019000001c0260080008000004001000000000c001001000000802200080040000000070004002002002800c0040050000008002003000000c010002003803800000a0058000002002000800000c017000001000a000
  | 0, 7 => 0x800001201a0000008012002002004000a0000008030000008000000400000b0008004004000003808c000006003800000001100380040460050158000000000008800000000000a803000200000b800c000000001000000e006000000400000200000ac004012
  | 0, 8 => 0x140040070000014002002000000000c011000002c000003005800c002005000801000400700a001c00e0100000008024000002800001001e0018028006000004001000e01f00a8008020000002803000600200100000200000020014000000001800400a006
  | 0, 9 => 0xc000002002800000400a00000000040000000018008000009800000a002001801401000000180240020030048060004001004005000a00000e802001600000000040000000010000002000004802400a00800800540000040000010006000000803c000000
  | 0, 10 => 0x80050018038014000
  | _, _ => 0
def thetaSlotBlocks : Nat → Nat → Nat
  | 0, 0 => 0xd213108d00011f0000350c30000a60220270000d000000101f0c705200012608011d0d701d0dd08c0a90380001100651060c900000011a09005900009d0910ea02a05e00412d00e08503603a0a50500200000000b60000e40000d5028001000
  | 0, 1 => 0x8a07006c13401e0320fa05f04b0df04d12e05b0310bd0030230000000000160da0480f50ca0ad0ab0b90210b801b1231150130d310004c03e0dc06d00808300008e09e0e80e10000000410d406e09811610106602900f0000cd02b11c0020cf
  | 0, 2 => 0x740f107d00000003900009c0000bc0000100000d60000000001390a70151270060940000000b411e0190ee09907600000000001710d00000000009610c0000571210000000b110800006407f0000000470000c600012b0000ae092018109
  | 0, 3 => 0xce13212c10708212a0bb0090790d901200a00500007b05607e05a0730e303c0000ec0000b500008704505307c05c03b00006908609f04a0000eb0db08b0000000000de00011201a1240b70aa0d804406b0710540000000000000610a8000000
  | 0, 4 => 0xf20be04f0e90f90c00fe1190b006300b0f60f812209b05503304e1280f00300ac0d10ed0a40780000e606a02d00010f00011b00d0ff0ef01100009310a0000261130370000000000c50000720bf0000000510000000a110e07500009a034
  | 0, 5 => 0x1290070000000670c20e20000620580e502e03d0430c40000c800c0401031330cb0a000001c0000000001300000951040000a30b302f0001170460e00b20f31180f700012f0ba1020af0970a20810680000841360f413808900000012510b0fc
  | 0, 6 => 0x401400100e00000500200f00000601100001000c00000000000000d00700301201300b00800900a0250001370c113a00000002c00000000011404905d13511107708f01403f06f00007a1200600000cc0000e70420fd0881050000240000fb
  | 0, 7 => 0x1eb1b40511fe36135714400037e1f123000003f21c1d60000000001042bc0a935c2da0000a40000000a024a33701900028f14b1701b000035e2b60000000002e72d00a615a35f33c0001713050000000000001c200000012d08c1c02a916c0b3
  | 0, 8 => 0x32814c0001e62331ac22b2e60001310002862e500029211a3751cc28003e3873900000001f617d00000006f3310000001df1600fa04700026509200000400031837a0002eb0002823043131131cd28301210618a0c119e31f2020521c61c7022
  | 0, 9 => 0x2db09f00000018000000000015705f24b08700030236b10f00033528e00000036600016b3640000000050ff14d37d23d3110000cb09a1c30bd05e00010a00024404308f2710002e229920b0000ab0b50333451010b400001526010d000141321
  | 0, 10 => 0x28c0d605a1dd12633d04a29300004f3082642a623727022e33e27803521a00016e34e0010001070002e42aa1b31c400331914300025d0d700031535909924925a0e20783862cb00038f09d0000132f50403792c401f1fb24d1cb00034a15d000
  | 0, 11 => 0x18d23b2e332b38a2460000002ee02e19f0020002510000001d802d1a03492bb0e52fc1650003500b111f37b04124f1460d831022d0c631b07126f1de2df3012150810a10551771a71820822d125804e1560860db3651b10e70c034112a3941b8
  | 0, 12 => 0x2b40eb1f31870000002d20002ac13a0ee2071a228a00000607018600000000032d0002e936f13d00000017b0000000002a80000001910ae27b0000c90001d02740002c700000000024129d2270bb0ce3581c90002f10002ec2fa2fb2432012f9
  | 0, 13 => 0x572130a52842140000912791cf00006c27308b0be3000ad00006300000000000000003112426d19011c30b26837300005828b0000180000002400000000000000002c31550000bf0250291bd36e1ea2cd2382591332ab0001c50982260e9
  | 0, 14 => 0x2881af10b25336010829e06a06907200000f0000000a81d32cf00003200006134d0000490ec1b527700c00000007d0d91381ca2281fc19b12c32617f3520001723840002031991962b707b1623160003090f100d20538c1ec23a14f00026b37f
  | 0, 15 => 0x3530003390000fb00005c10336336700000037c04b2471bf03c14823219a02604236219811d33617c0800aa0901a527503921215f1520e41ab0000140371ce0002bd00030e0001ee2de0003911b91ae18e0e823530d1fa0f629c24201b28703d
  | 1, 0 => 0xfd0b83200000d315b1fd0c70772500000003542af0003332cc0001ad00000024811533b1350001630000000000ed33026c01e3291e82a70003890f90000003930000000001a40960000091541732c50dc0000fe0002a12fe016188000000000
  | 1, 1 => 0x34023423e27c0440000000001202080b914a0d50000002a51000340002d50e60b62b200000016a0002be0000000000001ff01a0970001970000000ba05d0001140101890fc29623c17e0002b900005923f1d10de0d404629f221130298348000
  | 1, 2 => 0x2f00d103608e2ae2182ce08a0003422d40302190b20c21b72573680ca2ad0000a727a15100032a0531d93511d70000002562970003810242f800001d29b12e18b0000003170001640c528d1bb0751dc0002b00cd31a07916f1e431e32e1920a2
  | 1, 3 => 0x17427d0ac25e0cc0001782f21d40450b01850dd1f403b06226706b21f0742d631d1b210c1a638e1790892b11b601712825b23125f2c61762952912a317a00002c1672dd12511912919d35d2bf0000000001e902f1aa0001f21c8000000000008
  | 1, 4 => 0x2720002b30000000000001e00000000000000000da0c800030708d2061ba0df0002e812126a1e200009421632c07c00027f35b24e30c3690f310e00000017501c0000000002b800009300000025c26e1320001f72a42c12811f80001ef0001a8
  | 1, 5 => 0x2892d737813e32433f2610483431bc2ff10900000038014000000000000000034418c0001f91230000000f000000025200000002b0e00000002b530f0000002c906e15c03a00038538d13c0002450001be0000000ea1d21a10bc000382
  | 1, 6 => 0x2850652ef07e21d33832f0000000002ea0c322031c1611a32c21452f421e00000034c00000000000037200012709e00035a07a0000f20001a914e00000029030a20d11602a0d20882633772a22ed30318400012b20002713609c36d000000
  | 1, 7 => 0xd03922e106732227e33a1d52d82942f32292253323760001691832c031216838b00015e23600020f0002111db0503701f00c42ca2690e100022a1181e50001101e708305b0a300e3471da0f800014700000022200021034b11b05613702134f
  | 1, 8 => 0x12f0070762d30540112c811e0000680af26200033411714200007300013f0003250601932550f422f1c102819438820a00000000036c0b72f712237135636a0001f500010534600006d29a0e313b0001342092fd1492ba2231ed159000
  | 1, 9 => 0x2e00ef2173830000000000002542dc2a00850380202760f700021b22c1810002f604d00000b00000002324c1502242d90001e10001121583550cf00018f08406632300a00023910206420420e19509b37404c0f500009526620c1e3000139
  | 1, 10 => 0x1903600001800000004806503b08207d00000001000006a03500006804505300002f05d00003f08303706603c06403a07601d00000000007700000607305900005f00000000016616d00000000032719c07f000000000000306111153314000
  | 1, 11 => 0x4201700000000004300000000000900000000000000005505b00000001a02d03103304b02900d00001201e01402c02200305406307c00406104a03000c04905e07204606005701f02101b067023000000050000024040075
  | 1, 12 => 0x6e06204c02a07a07b00e00205a06f03e00002b00706c07104107800a05101306d07e08004707002e05604e00005200006900001508105803802806b00800b03904f03400504404d07407900001c05c00001603203d02502700100f000
  | 1, 13 => 0xde0bc00a08006f1330af12301814b0010200a705c11511a04b0000000b811e1000390480a105e14a0000a308700000309f0f300512c0000d11051130fc0000c10ff0cf0000fb00000004d0b903100000015710f13d0070c706302601102007f
  | 1, 14 => 0x1450000510020a814c1470b40000dd03614f0a51300000aa07e0a00700b015101e1060080e312f12e0d207913100010100009009515811f0000f20000000880000c90e10c006d0000df0770000f016406b0240ea12016310315a0600f5
  | 1, 15 => 0x13400000000001c1180cb0b70100b20000ce09b08b03515f12a09700008d09613915d0f60f40c50000670910f911100009d00011b0c30221420da04f0590000751240e204e0830000850fa02d00011203f0000000000e900014e04c14004105d
  | 2, 0 => 0xa911d15c01b01909c1601431410ad07808e0e006609806c15e07214d0d715609204212210d02f1381080d50d400011400000000010b00011601700000004510e13e16211c01d12100004703300008100000004300e0490000861590000000b5
  | 2, 1 => 0x580760e80ba0610280c80ef0b612b0000000c205a0001370000000000000840261070000e40a600013a0a400013f14900015300016504613b0710d308213c03b09907b08c00007d0000001320290000cd0be10205b0f707f00009e06a009068
  | 2, 2 => 0x3d00000009303200000b0550150340440160ed0000000ee00d0000b10e700f0620000ec0500f103713600012d00005f0120db0b309a0fd0d900007c00400000000004a0110f80520d007300014807a0540000560a200000004001306401a069
  | 2, 3 => 0xbb09403806510a0000000000000000bd00014602e03a1540e60eb03c0000140890ac00000000000000000010c00011000002c0000000d607402b0dc15b1290ae11905303e0000000001281610bf03000000005708a0ca00000012606e117135
  | 2, 4 => 0x9d00003904409c09000000004606103e09f09706807f06303006b00d08000000009604c00503b05201b05b07102502a08f0230e51091520001551040000000c40cc1440001500210000270c612701f0000000d80000060ab1250fe00000c000
  | 2, 5 => 0xa402000007e05a00000003c00004701701d05900000006403d0a600000007904a0000320360a900000005602b06600005e08400002c00006c02702a00000004202800400000006d05300108d0a801302e04b09b01e08c01806202f0510500ab
  | 2, 6 => 0x490a508e05d0aa08a00000007001902907c09500603f0000250a104e0a207808800007601500203807b00805f03103705c05406f0a303404f09408200a08709e08109a01a00000002600000000b08b0000400a000000707405806a077
  | 2, 7 => 0x8600000c0000720570480000000000650000890000120a701000009804d06009107303a05501102101606e02302407d00006900000004303500004100000000308f03300e00900009200000008300000002d00000000004501f08501c06707a
  | 2, 8 => 0x100000e01400100701300001100000d00f00600000000c00000000a00000000001000200800b01200900400500300000000000600000200000500100400300009907509301402200f
  | _, _ => 0
def thetaStateBlocks : Nat → Nat → Nat
  | 0, 0 => 0x5c1507c7b970541efee5c006df40d3dc20fcb1501a7b902df82a034f72e0a80d3dcb05bf1501a7b97001e7a034f72e0a83dbdcb82819787afb97029d07a7b970541e7ee5c150797b970540e7ee5c15078fb970541e1ee70f0541dfee5c150777b979781056fb97001dfa0adf72ecf050edf72e0a83b3dcb82a0ebf72e0a83abdcb0e9f150227b97054089ee5c01d1e8113dcb82a0e7f72e0035fa0c7ee5c150737b9c3c150157b8397b82a02af72e0a105e055ee5c14397c0abdcb828727813fb970021fa027f72e0071f404fee5c0e3fa809fdcb070f15013fb970021fa06ff72e0b838bdcb8281a7870fb9705c0ddee5ddc5c0c9ee5c00b5f80c7dce1e0b80c7dcb82831f818fb9700707e6
  | 0, 1 => 0x5c021beb3910cf800efd672e003bf59cc00b9e077eb39700597ace5f5c0597ace5c00cbeb3970085face5c0a759c42bdc0a759c83b7c0a759cb109f0a759cb8111ea759cb80423d672e0107f59cb828837e72e0a20bf9cb828827e72e0a207f9cbd38a065f9cc5e0a065f9cb828197e720ebf05032fce582378a065f9cb828817e72e0a203f9cb828807e72e05387ffe72e003bf0fefce70f05074fce60a83f7f3970541f9ee5c1507dfb970117c5038f783b82a038f72e0a80e3ddc087f1501c7b9700437a038f72e0a163e071ee5c1507d7b97050b0f03df72c0dfc5407bee5c1501efb842fb82a03df72c213c5407bee5c0affa80f7dcb81ae82bbdcb82a0f9f7
  | 0, 2 => 0x18b82378ab39608de2ace589678ab396257e2ace589578ab3960a1e2ace5f5c559cb129f15672c4a3c559e0ec0afc559cc127f15673049bc559dc125f1567302dbc0dead0fae013feace6005cfab3c1e00b5fab39700927ace5c0247eb39700917ace091ee00b4f59cb80487d672e0120f59cb8047fd672e011ef59c20fcb0079eb3902df800f3d672e003cf59cb05bf0079eb39823be00f3d672e011cf59ce1e00b3f59c823fc0167eb397008dface5c0235eb397008cface5c0231eb397008bface413be0089f59cb8045bd672e0115f59cb80453d672e0113f59cb8044bd672e0111f59cb80443d672e010ff59cb8043bd67
  | 0, 3 => 0x16051e2ace58a7f8ab39629de2ace4537e0ab3902df82ace4533e0ab3914bf82ace62f0559c8a57c15672293f0559c8a47c1567228ff0559c2dff0f0559c8a37c1567145f70559c513dc156783b82ace287ee0ab38a17b82ace283ee0ab38a07b82ace5c156713ff70559c4fbdc156713df70559c89e7c1567208ff0559c2dfc11fe0ab3913bf82ace413be0ab3913af82ace589cf8ab3842fb084f15672c4e3c559cb137f15672c4dbc559c816f82df8ab3960b7e2ace589af8ab396269e2ace5899f8ab396265e2ace583bf8ab396263e2ace411fc4c3c559cb12ff15672c4bbc559cb12df1567
  | 0, 4 => 0x1700b97ace5c0d759c8277c0d759cb08bf0d759cb805c7d672e0170f59cb805bfd672e016ef59cb805b7d672e016cf59cb805afd672e016af59cb8014bd672e0169f59cb805a3d67208ff002d7ace5c02cfeb39700b37ace5c02cbeb39700b27ace5c02c7eb39700b17ace5c02c3eb39700b07ace411fe028fd59c8affb156722bdec559c8aefb156783b08af15672c19fc559cb15cf15672c19bc559cbd38ab39075fd38ab3962b7e2ace58ad78ab3962b3e2ace58ac78ab3962afe2ace58ab78ab3962abe2ace5ddc559c8277ddc559cb154f15672c54fc559cb152f15672c547c559cb150f1567
  | 0, 5 => 0x637dc14ee9c8277c14ee9cb08bf14ee9cb8319f4ee9cb80227cee9cb828c5fa72e19c50b1f72e0e3d032f72e0a862bdcb82a03ff72e0a8627dcb82a188f72c61fe05b772e0ab6ee10bee0ab6ee584278ab6ee5c150c37b9705430bee5c150c27b81f7977717396307f05ce5c182f1739c3c006bf739700c0fdce5c045f010df9cb800dbc0f3f39180f702ce585cfc0b3962fff02ce58bf7c0b3979781672c5f7e059cb17cf81672c2e7c143c2ce5815f83c7859cb82f7e1672e017af59cb805e7d672e0178f59cb805dfd67317802e3d672e0053f59cb805dbd672e0175f59ce5e005cf59cb80233d672e0174f59cb805cfd67
  | 0, 6 => 0x17055812be0b801ebc23fd8e1ece17fe2b1611be343e2b1617de6715885efc14eec341ee019ff4c62f0047fa6072f70021fa62e02a7adbb1611de11be331617de0f1e330cf7b801ebf310bdf0bcf17341d846f8b98e1eee2e63170bbf0b3170677d662c0dfc153d669390baf15672e0538417e703ef2e0a7772e0053f19cf4f572e0052f4e58cdfc153960f3f054e58cd7c15396115e67153970ce2a72c0afcce2a72e0ccf8a9cb8331e2a770ce10fe2a72e19c65fea72e0196fa9cb80657ea72e0194fa9cb8064fea72e0192fa9cb80647ea72cce0127ea72e0190fa9cb838f539608de38f539700c7fd4e5c031df53970ce021bd397053ba7
  | 0, 7 => 0x1705586fbe0b82ad4781bdf7055a8f05c0379eb51e0b82a027fa3c1705586efe0b82ac375f05c1561b9f82e05bac371f05c1561b7f82e0ab0db7c1076f82ac0f9f05c1501ef83e7c1704dea06ff82e0b81bbdcb827170377c1705581bbe0b82ac36bf05c006bf70327c170558193e0b82a1f0327c17054055e369f05c1561b3f82e0ab0d97c1705586c7e0b82ac361f05c1561aff82e0ab0d77c170558247e0b82ac35bf05c1561acf82e0ab0d5fc02af9705c063f05cee0b80c7e0b800b3ee031f82e0ab018fc1705068fc063f05c1561aaf82e0ab0d4fc17054055e351f05c1561a7f82e0ab019fc17055869be0b80243d607bf82e0ab0d2fc170558693e0b82ac347f05c1561a2f8
  | 0, 8 => 0x170540e7ee5c156073f82e0ab0ed7c15cb81060fb8ecf97054183f05c1561d8f82e0a8113dc8ebfb82a044f82e023d4089f0e023d4089ee5c156044f82e09c540c7f05c1561d6f82e0ab0eafc55cb82a02af823a9ee0a80abe0b8074fea02af82e0ab0157c17055874be0b82ac3a3f05c1561d0f8ab9705439ff05c1561cef82e0ab0e6fc1617ff05404ff05c05df15013fc17002b7d404ff05c137a809fe0b82814fa027f82c733c55809fe0b82ac04ff05c150e5f813fc17055872be0b82ac05ff058e4f8ab017fc170558723e0b82ac38ff05c1561c6f82e0ab0177c16057e2ac05df05c1561c5f82e0ab0e27c17055870fe0b82ac385f05c1561c1f82e0ab0e07c1700297ac181f05c1561bff8
  | 0, 9 => 0xb828f9fad05c147cbd682e0a3e3eb417051f0f5a0b828f7fad05c140a7d682e0a3ddeb417051edf5a0b828f67ad05c147afd682e0a87abf402079705032fd05c140cbf397055b8197e82e0a80cbf4170543d3fa0b82a1e8fd05c150f3fe82e0a879bf4170543cbfa0b9dc1424bf417054125fa0b82a1e4fd05c150f1fe82e0a878bf401f79705074fd007de5c150fa0b82a43e8209df05487d05845f8a90fa0b80227d21f4170543c3fa0b82a1e0fd05c150effe82e0a877bf4170543bbfa0b82a038f72e3dc54071f05c05ef1501c7c1705580e3e0b82a03df72e0ab01efc17054870aef82e0ab0ee7c17054069ee58617c1501a7c1705580d3e076fcb82a073f8
  | 0, 10 => 0x12fcb802d3d682e003cf59cb0c2f800f3d682e0a407eb41705202f5a01afcb80243d682e09b8487ad05c14807d6805ff2e00c3f5a0b829007ad05c147ffd682e0a3fdeb417001dface5c094f0077eb417024fc01dfad05c140efd682e0065f59cb80d5e0197d682c0dc197d672e01b832fad05c13a9d670b97029d681fdf2e053ad05c13853ad0581ba9d672e01ba9d683001d4eb397001d4eb417003efa9d682e023a9d687011d4eb397051fcf5a0b067f141a7d682e0a0d3eb417d7141a7d682e0a3f7eb417051faf5a0b828fcfad05c147e3d682d2f00fbfad05c147dbd682e0a3ebeb417051f4f5a0b802e3d6eb417055bad041d7e0ab75a0b046f156eb4170061fadd68
  | 0, 11 => 0x5c043df5682e021dfab417010e7d5a24e5c006bf5692e0035fab41700167d5a0b8086fead05c0435f5682e0219fab417010c7d5a0b8085fead05c042df5689397002b7d5a4b8015bead05c042bf5682e0214fab4170109fd5a0b8084bead058337823d5a18337823d59cc5e023d5a22f011eacf077011ead1001c8f5670370391eace5c0423f5682e0210fab4170107fd5a0b8083bead05c041bf568072f7004bfd5a0b8025fead0e0097fab39704dead05c0419f5682e020bfab41701057d5a0b80827ead05c0411f5682e0207fab441dc012df5682e0096fab438025beace5c012bf5682e0206fab4170102fd5a0b80813ead05c00a5f568
  | 0, 12 => 0x2e023cfab417011dfd5a0b808ebead060098fab3904cf80263ead05c0131f5682e0239fab417011c7d5a0b808dfead05c046df5682e0235fab417011a7d5a0b808cfead00c1ee0039fab455dc0073f568042f7001cfd5a0b800e7ead04107dc0073f5696061f001cfd5a0b808cbead05c0463f5682e0230fab4170117fd5a0b808bbead05c045bf5682e022cfab4170115fd5a0b808abead05c0453f5683002e7d59cb80173ead06049f805cfab41701147d5a0b8089fead05c044df56831ee02d7ead05c044bf5682e0224fab4170111fd5a0b8088bead05c0443f5682e0220fab417003efd5a0b8087fead0415fd8049fab416970093f5682e0049fab416f70093f568
  | 0, 13 => 0x580c5fab3970062fd5a0b80933ead05a5ece01fbead25c00fdf5682e024bfab41701257d5a0b80927ead00c3ee004ffab449dc009ff5682e004ffab41704e0923ead25c138036fab4970123fd5a0b8091bead05c0133f5682e0245fab41701227d5a0b8090fead05c0485f5682e0241fab4170029fd5a0c0189f5672e00c4fab41701207d5a0b808ffead05c047df5683011efd59cc051f03d59ce9c01eace5e9c01ead06ee00f5672eee00f568206fe00f5672c0dfc01ead040a3c01eace58147803d5a0123e003d59e0f001eace6003d59c816fc007ab418bc007ab40247b800f56883b800f5682e003d5a0f5c01eace5f5c01ead040dc0f567
  | 0, 14 => 0xb80983ead05c04bff5682e025efab417012efd5a0b0193f5672e00c9fab4160323eace5c0191f568205be06f567317037ab3c1d81bd59cb037ab397a7037ab41697b381bd5a4bbb81bd5a0b028f037ab4102df806f568317806f56883b806f56809cf2e01bd5a426fcb806f5692e01bd5a0beb81bd5a0b028f04b9f5682e025bfab417012d7d5a0b018ff5672e00c7fab417012cfd5a0b80963ead05c04aff5682e0256fab417012afd5a0b018df5672e00c6fab417012a7d5a0b0135f5672c1c3c04d7d5a0b8026bead05c1382a7d5a0b8094fead05c04a5f5682e0251fab41701287d5a0b8093fead05c049df5682e0088fab417a7049bf568
  | 0, 15 => 0x17032fc55a1c0cbf15672c22bdee2ad05c7b8ab416057ef715682e13b78ab41709d7c55a24e602c78ab410a1f80b1e2ad04107e02c78ab4170163c55a0b84e9e2ad05c273f15682e13978ab41709c7c55a20ee02f78ab417017bc55a0b84e1e2ad05c0a0f156871ee10fe2ad05c26ff15682e13778ab41701abc55a0b84dbe2ad05c26cf15682e135f8ab41709abc55a0b84d3e2ad05c268f156809ff2e01d78ab483679700ebc55a41afcb8075e2ad25c1381d78ab497099fc55a0b84cde2ad05c265f15682e13278ab41704e13de2ad25c263f09ef15692e015682e00affab41701317d5a0b80987ead05809dfab397004efd5a0beb809dfab416032beace5c0195f568
  | 1, 0 => 0x103cb046f15682c11bc559cb808de2ad0582878ab390a1f60a1e2ad05c050f15682e14578ab4170a27c55a0b8511e2ad05d9ca1fc55a0b850de2ad05c285f15682e14278ab4170a0fc55a020fcb138ab417a7138ab41777138ab4160e1e2715682c0dfc4e2ad05814789c55a0816fc138ab418bc138ab4104cf82715683878271568048f704e2ad107704e2ad0137e5c138ab49704e2ad05828789c55a0beb89c55a0b8505e2ad05c281f15682e06678ab4170a03c55a0b84ffe2ad05c27ef15682e13ef8ab404e79701ffc55a4b80ffe2ad05c27cf15682e13df8ab4021796057e2ad05a5c0afc55a0b27af02bf15682e015f8ab41709e7c55a0b84f1e2ad05c277f1568
  | 1, 1 => 0x16559f055a0b2abf82ad059557c15682c1dbe0ab416553f055a0b2a8f82ad019be4203e0ab41738407c15682ca9fe0ab41654df055a0b030f82ad05952fc15682ca93e0ab416547f055a0b2a2f82ad05950fc15682ca83e0ab41653ff055a0b4bc15682ca7be0ab4160cff055a0b066f82ad0594efc15682ca73e0ab416537f055a0b29af82ad0594cfc15682ca63e0ab41652ff055a0b079f82ad0594b7c15682ca57e0ab416529f055a0b293f82ad059497c15682ca47e0ab416521f055a0b28ff82ad059477c15682e4156804bf2ca37c55a0b05bf15672e02df8ab4170a33c55a01b7cb077f15682c1dfc559cb80efe2ad05c28bf1568
  | 1, 2 => 0x4b4bdc156825a3ee0ab412d0f7055a0967fb82ad04b3bdc1568259bee0ab412ccf7055a0965fb82ad0433bdc15682595ee0ab412c9f7055a09647b82ad04b1fdc156820afee0ab412c6f7055a0851fb82ad04b17dc15682589ee0ab412c3f7055a09617b82ad04b07dc15682145ee0ab412c0f7055a095ffb82ad04afbdc15683e77055a095efb82ad04af3dc15682577ee0ab412baf7055a095cfb82ad04ae3dc15682e77055a095bfb82ad04adbdc1568256bee0ab412b4f7055a0b2b3f82ad0081e41d7e0ab41047f82ace5823fc1568209df0559cb2b2f82ad05958fc15682cac3e0ab41655ff055a0b2aef82ad05956fc1568
  | 1, 3 => 0x5e7e5c15682f2f2e0ab4178f97055a01b3cb82ad00d7e5c15682f0f2e0ab4068f97055a0bbfcb82ad05dde5c15682edf2e0ab4176797055a02a3cb82ad05d7e5c1568040f2e0ab4053f97055a0babcb82ad1272e0ab4174f97055a0ba3cb82ad05cfe5c15682e6f2e0ab4172f97055a0343cb82ad05c9e5c15682e3f2e0ab4171797055a0b87cb82ad05c1e5c15682dff2e0ab416f797055a029bcb82ad014be5c15682ddf2e0ab416e797055a0b6fcb82ad05b5e5c156825c15682e0ab392d9f7055a096c7b82ad04b5fdc156825adee0ab4025f867fb82ad0433fdc156825abee0ab412d4f7055a08527b82ad04b4fdc1568
  | 1, 4 => 0xd5f2e0ab418df97055a0c6bcb82ad0633e5c1568318f2e0ab406a797055a0c5fcb82ad062de5c1568315f2e0ab418a797055a0c4fcb82ad0625e5c1568311f2e0ab4188797055a0187cb82ad061fe5c156830ef2e0ab4186f97055a0c33cb82ad0617e5c156830af2e0ab4184f97055a012fcb82ad0611e5c1568307f2e0ab4069f97055a017fcb82ad060de5c15680d2f2e0ab4182f97055a0c13cb82ad0607e5c1568302f2e0ab4180f97055a0183cb82ad0601e5c15682fff2e0ab417f797055a0bf7cb82ad05f9e5c15682fbf2e0ab417d797055a0be7cb82ad05f1e5c15682f7f2e0ab417b797055a0bd7cb82ad05e9e5c1568
  | 1, 5 => 0x20798bc156833df2e782ad0172099f055a02e70f055a0183e4ee0ab4025f8247b82ad00c3e085ee0ab405e0ee0ab47dc35fdc156804df2e0ab419e797055a0cefcb82ad0675e5c1568339f2e0ab419c797055a0cdfcb82ad066de5c1568335f2e0ab419a797055a0ccfcb82ad0665e5c1568331f2e0ab4036f97055a0cc3cb82ad065fe5c15680a9f2e0ab4197797055a0cb7cb82ad0659e5c156832bf2e0ab4195797055a035bcb82ad0653e5c1568328f2e0ab4193f97055a0c9bcb82ad064be5c1568324f2e0ab47dcb82ad0647e5c1568322f2e0ab4190f97055a0c83cb82ad063fe5c156831ef2e0ab404ff97055a0c77cb82ad0639e5c1568
  | 1, 6 => 0xb8014fd67397800eb39797800eb418014fc0eb3970029f81d682e0053f039f5a0b80233d672e008cf07df5a01afcb800b3d682e09daeb385cb81aeb4055f97035d686397035d682b97035d682149ee06bad05c1386bad0581bb5d672e01bb5d683001daeb397001daeb41797808eb417035c8eb4381ae4759c17fcb826eb4025f970021fad014be5c0087eb41704e010fd682e09c14bd672e0052f59cb82700a5eb41704e01c7d680b97002d7ad05c13805af5a0c5e09eace5828789eace5c138557d5a082bff9d8ab449cb067f15682c19fc559cb066f15670b97a71568040f2f4e2ad00d9e5d9c55a082bfbb38ab4025f960e1e2ad00dbe581478ab431cb028f15680b98bc1568
  | 1, 7 => 0x1800f56ddcb800f56de18e5e5e0ce572e0036fcec72e06be76398bc173b1e0ee0b9c357cb82e70d1f2e0b9c8517b82e703ef2ecf05d05c0a0f173970117c283c5d007de5c03af1741704e00dbee830117c01ee73001b781ee72e0036f03dd0428fdc00c5f7410a2f700317dd05c138062fba0c007062fb9cb800e0c5f7402af97001afdd05cee0035fba18e5c0a7ce07de5c140a7f415cbd3859cae5ddc2ce572c0dfc2ce572c0a3c2ce57048f702ce1a1e5c0b3852f9702ce4293dc0b390cef702ce172f2f02d0c72f2f02d0572f2f02d0599ffc0b3961b1f04e1682f2f04e1682c363e015f85a0b827078f0b417978127e1682d2f019f7ad05e5c0dd672f2f00dd68
  | 1, 8 => 0x599c0dea72e19c0dea80b982703d4e173001ea730ce00f53970ce00f5405c81b81ea72e7701a0fd51572e0056faa02ee023d4e5c33823d50e19c11ea70bb03723d4e17800e47a9c2e5c1c7aa0103cb838f54053797071ea82e09c71ea82c0df8f539700df8f541800fc7a9cb800fc7aa0b808fc7aa02e5c0a74e572e03ba72e09e9dd385cb829dd4055f97053ba86397053ba8340f2e0a7750572e0a77505c138a7750581bd3ba72e01bd3ba83001e9dd397001e9dd417011e9dd43808f4ee9cae5c080ffdcb8271501ffc1606f501ffb9700dea03ff83001ea03ff72e003d407ff0172e0ab6f05c138ab6f0581bd5b772e01bd5b78
  | 1, 9 => 0x5cb808be2bb1cb86715c2ec72c0deb85cb800dbeb85d8e6003d70b9700317d76397071ebb1cb829ddc2e572e04e172f2f0272b970ce1385cae581ba70b95cc0074e172e06ba70b95dc0474e172e0043f4e172e005af4e172e09ea72e09ccf5385cb80a3f5385cb8155f5385cbd38a9c2e5ddc54e172c0dfc54e172c0a3c54e17205bf054e1731782a70b904cf82a70b9c3c15385c123dc15385e0ee0a9cd13cb82a70d3f2e0a9cd0fcb82a7342f2e0a9c34bcb82a70b97054e14de5c153960f3f054e172fae2a70b970ce2a82b970ce2a82e09cce2a82e19c17bc5505c0d9f153970ce1b3e2a80b96271bd4e172c0dea7
  | 1, 10 => 0x104cfbb8ab3977715672c2ebc559cb028f15672cd63c559cb357f15672cd5bc559cb355f15672cd53c559c86dfc1567205bf0559c9a9fc156783f9e0ab398bc15670dcf93b9e0ab40397e1e0ab39352f82ace4d47e0ab39350f82ace4d3fe0ab3934ef82ace4d37e0ab3934cf82ace697ee0ab3c1dc156734af70559cb82ace59a4f8ab3c1df5c559cbeb8ab39816de2ace436fe02a7d59cb80d23d672e0347f59cb0bbf0a759cc5e053acf572e053ad05c0a759c207cb4badd672c0dfc2dd6738782a1f3c9cc1506d7e82e0a8d1bdcb82a345f72e0a87063f70bb1cae5c0e17639705763960f3f057
  | 1, 11 => 0x2e0a8dbbdcb9dc0d7ce5ceeee2e7387b3c173970db7c5cf0770117c5ce70f00ebc5ce5c06d9f73902df800dbee72e007afb9cb801ebd4f9ce1e0a053f9cb829b5fe72e0a6d5f9c820fb037f0b39b4f9702ce62e9781672c23be059cb368f81672f2f02ce58477f5c2ce5c367f0b39701b37ace5a5e02a7ace5ddc35d672099f035d672e06bace5c06cbeb398bc13759cb80a9f3759cb80d93d672e0363f59cb80d8bd672e028f82d7ace5c06c3eb39701b07ace5c06bfeb39701af7ace5c06bbeb39701ae7ace5c06b7eb39c3c051fab3966b5e2ace62fa715672f4e2acf0776715672c2f3c559cb359f1567
  | 1, 12 => 0x1b7cb82ac0f7f25c138ab03dfc9704e2ac6eff2172e0a812be0b82ac095f05c138ab0257c9606f5604af82e01bd5812be4c007ab0257c17001eac095f25c045f338ae5cee0a7772f2e6edf0272e03c799c27ab970021fa7ab970038fa721bbee19ea72e1baf8a9c207cb338a9cf9d99c54e5d9cce2a783b867153970ce2a72c253cce2a72e0374fa9cb80a3f37a9cb80dcfea72f4e38f5398bc1c7a9cb838f53970047fa9d39705372f4e5c0d73ba72e04f7d3ba72eee29dd3904cf829dd382afb829dd397053ba72e0a77082f72e0a80ffdcb828587eddc820fb816ddcb037f156ddcb82adbb9702dd6ddcb82a371f72e0a8dc3dcb82a36ff7
  | 1, 13 => 0x2e01bd580bfe4c007ab017fc17001eac05ff2172e0a80bbe0de7cb82ac05df2172e0ab0177c9704e2ac05df2581bd580bbe0b806f5602ef93001eac05df05c007ab0177c9704e2ac181f2172e0aa8f0c72e0ba8f0572e05a8f05c13d5a8f06f1e5c156a3c85cb82ad4796397055a8f25c138ab51e4b037ab51e0b806f56a3c9800f56a3c17001ead4792e023d5a8f2e023d5a8f06003d581bfe0b800f5606ff92e0ab0327c05cb82a059f82b9702c0b3f05c138ab02cfc9800f56059f82e003d58167e7ee5c156091f92e0ab048fc1704f56031f82e0ab018fc1704e2ac063f2172e0a837be0b8271560def90b97054067f0153e5c156033f92e09c5580cfe4b037ab019fc1700deac067f26003d580cfe0b800f56033f9
  | 1, 14 => 0x5c0379bd5a4c0079bd5a0b800f37ab4821797004afd5a4b80257ead1272e0a0d3eb49705069f5a0ae5c0b75a02e5c156eb4820797055bad25c138ab75a4b037ab75a0b806f56eb49800f56eb417001eadd690a8f2e0a053eb49704e2814fad2581bd029f5a0b806f40a7d693001e814fad05c007a053eb497054125fa0b827150347e93001ea068fd05c007a81a3f485cb82a074fd2c72e0a87d0572e0487d05c13d487d0172e0a90fa42afcb82a43e9639705487d2572e0a90fa4b8271521f49606f521f41700dea43e93001ea43e82e003d487d25c047a90fa5c047a90fa0b82ac055f0581bd580abe0b806f5602af92e0ab013fc05cb82a02ff82b9702c05ff05c138ab017fc9606f5602ff8
  | 1, 15 => 0xc800f5682e4007ab49827007ab41704e00f56931ee00f5682e3dc01ead2601d7803d5a0b8075e00f56930003d5a0b8001ead240dc0f5672c0dc0f568300dc0f5682e01b81ead2600381ead05c00703d5a4b9dc06f7f5692e0039fab41800e073f5682e00381cfd5a4c0070dffab417001c37fead25c00fbf5682e0049fab41800e093f5682e003824fd5a4b800d7ead05c13802cfab49606e059f5682e01b8167d5a4c00702cfab417001c0b3ead25c00adf568fb97011ead25c7b823d5a5c7b823d5a0b8011ead2e0047ab41800e47ab417001c8f569800e47ab397001af91ead2e0035f23d5a0b8015bc8f5697002b791ead06f5e5c137ab49704e26f5692c0de6f568
  | 2, 0 => 0x16f7037ab4171ee06f5692c1abc0dead05c06af037ab49600dead05c006f5692c0dc6f5682e01b8dead25c0111f5682e007efab41697801fbead25c009ff5682c0dc13fead05c03704ffab497004cfd5a0b030f80267ead209be6003d5a3ee6003d5a02e6003d5a0183cc007ab449cc007ab455cc007ab402179800f56826003d5a0c007ab39057f800f5683e7800f5682083f001ead05cf001ead009be5c007ab4fdcb800f5690b97001ead20c1e5c007ab4c9cb800f569ab97001ead2085e5c007ab492e003d5a4b800f56820afee003d5a4f9dc007ab4973b800f5692dc007ab49030f800f5682c0c3e003d5a4a5e003d5a0b4bc007ab49b3c007ab41767800f569
  | 2, 1 => 0x169782715692ecf04e2ad259be7c138ab497209c55a4b827138ab4970333c55a0b80ffe2ad05c02bf15682e09c0afc55a42e5c7b8ab49704ef715692e02c78ab41704e0b1e2ad25c05ef15682e3dc17bc55a4b80d5e2ad05c1382ef8ab49701ffc177c55a4b8270acf15692e09c0ebc55a42e5c02ad2c72e015692b9700ab49700ab41704e055a4137cb037ab47dcb037ab4030f9606f568939606f5682581bd5a0b037ab39f3b037ab4173b037ab416061e06f5682d2e06f56804df2e01bd5a7ee5c037ab4830f9700dead3272e01bd5a49700dead25c037ab41f3b806f5692e7700dead258187c037ab49697806f5692e4037ab49627037ab41704e06f569
  | 2, 2 => 0x26f97055a01b7cb82ad0153e5c15680d6f2e0ab404ff97055a0353cb82ad00c3e5c156804bf2e0ab402ff97055a3ee172e0ab481f785cb82ad20bfe172e0ab4830797055a01b3cb82ad00d7e5c156806cf6397055a42a3cb82ad0081e5c15680a7f2e0ab405eae5c156925c15682e0ab39057f7055a0851fb82ad0172e77055a4b076f82ad0172c203e0ab4b1cb4bc15692e4156804df2e09c55a7ee5c138ab4840f9704e2ad2172e09c55a58e5c138ab4c9cb82715692b9704e2ad3572e09c55a410bcb8271569055f2e09c55a435fcb827156925c138ab49704e2ad04287dc138ab49f3b82715692083ee09c55a4b9dc138ab496e09c55a4b030f8271569
  | 2, 3 => 0x5cb82a70bc9cb82a80bd5cb82a80b82179705501725c15405cf9dc15405c820fb82a80b973b82a80b96e0aa02e58407c15405cb030f82a80b969782a80b976782a80b9720aa02e5c138aa02e5c7b8aa02e5c05df15405cb8159e2a80b9700ebc550172e015405cb037a9c2e5c037aa02e5c06fbf5405cc007a9c2e5c007aa02e5c0059f5405dc047a9c2e5c047aa02e5c137aa02e5c156ea02e5c140a7d405cb82a068f80b970540e9f0172e0a90f0c72e3dc5d0c72e01747dcae5c0b405cae5c0b4053f95cb81682bd5cb81682b973b81682b969781682b976781682b9704e1682b97005a3ee5c13d5a0b82702bfab41704e0b1f568
  | 2, 4 => 0x5c151ca7e82e0a8e4ff4170541b5fa0b9dc15031fc170177c5405ff05c15602ff82e0ab1c97c170558e47e0b82ac05df05c156390f82e0ab1c7fc55cb82aa3c170038fad478abb82ad4782e0ab51e0b82ac71df05c15638df82e0ab6e0f9f05c0b7581f3e0b82ac719f05c15638bf82e0ab1c57c170558e27e0b4bc0b02cfc1697156059f82e0ab1c47c170558e1fe0b826eb019fc1705580cfe0b82ac70df05c156385f82e0ab1c27c16051e2ac0f7f05c156383f82e0ab1c17c170558e07e0b82ac701f01763970570b95cb81385cb827a9c137c2e5c1547dc2e5c154066f85cb82a837ff0b97055007de172e0aa0dfbc2e5c15402ff85cb82a80b85cb82a8
  | 2, 5 => 0x171ee2ad0584a7bdc55a0b874fe2ad05c3a6f15682e028f8ab4170e97c55a0b8749e2ad05c3a3f15682e05578ab41700ab417002a7d5a0b80e8bead05c0743f5682e0036fab41701d07d5a0b80e7fead05c073df568939700167d5a4b800b3ead05c0d7ab41701cefd5a24e5c137ab4d5cb826f5692e09bd5a0b80e73ead05c0a759cb829cdfad05a5e05bad05c0acf0b75a0b826eb75a0bd38ab75a0c5e0ab75a0b82add682e0a053eb417053bad05c14e6bd682e0a733eb41705398f5a0b829cbfad05c151cb7e82e0a8e57f402af970543e82e770543e82e06ba43e82eee2a43e82099f05487d00abee0a90fa0b82a43e8
  | 2, 6 => 0x49cb82ad0779e5c1568048f2e0ab47dc10bcb82ad3072e0ab41ddf97055a097055a0b82ace4eebdc15682773ee0ab413b8f7055a086efb82ad04edfdc15683e77055a09db7b82ad04ed7dc15683177055a0373cb9dc15692e77055a09da7b82ad04ecfdc15682765ee0ab413b1f7055a0b3b0f82ad059d7fc1568939030f82ad058187c15682d2f055a0bd3c15682cebbe0ab41697b3c15692eef055a0b3adf82ad059d67c15682ceafe0ab416051f055a0b9055a24e5f5c55a0beb8ab3973ae2ad05c3aaf15682e19c55a0b8753e2ad05c3a8f15683e76f715682ecef715683e78f7156883b8f71568
  | 2, 7 => 0x5c15602ff82e0ab0177c17055a8f05c156033f80b97054e5c138ab41606f5672e01bd5a0c007ab397001ead05c338a9cb8677b8aa2ae5c05df15455cb826f5417071ea72e0e3d5ba8ab9705029f505c14ee9cb829dd21e0b82a03ff72e0ab6ee5ceecf05d05c045f7b8ba0820fb4bc0b4179781672e06bace4107dc1375a0b800b3e6eb4040f969715683e769715682f4e2ace5a5ece2ad05ddc559cb028f1567205bf0559e4e7cf055a0c5e0ab3c9cb9e0ab441dc1567ab82afb82ad0783e5c15683c0f2e0ab41dff97055a0efbcb82ad1f72e0ab404e797055a026fcb82ad077be5c1568
  | 2, 8 => 0x170559fee5c15689397055a097055a0b82ace7cee0ab4173b82ad058187c15682d2f055a0b9055a0b8f715682e015682e002cfab41704dead05c156eb41705029f5a0b82a43e8
  | _, _ => 0
def thetaOffsetBlocks : Nat → Nat → Nat
  | 0, 0 => 0x20fc8191f987b31e0075a1c9c6f41b3869b19bc649188c5fd175c5b1161455f14cc50013504ae122046210bc4090f583b00df43570cac2f80b14292097c22c07e41c6064c16004e810703840b50208056008c000
  | 0, 1 => 0x1fac7b81e4875f1ce470d1b9c6c11a88676192861e17c85cc1698580156853414384e212d8490117442a10103de0ee038c0d6432d0c1c2e10aec2880970236080c1d00674177051011103ac0b802140520098000
  | 0, 2 => 0x1dbc7491c8c6fd1b5c6b11a4866c191861a17d05ce16a0579153452713ec4d512bc489115843010283e40ef838b0d603320bfc2cc0a9827a091c22107ec1d506bc189055813004280e402f809801c804c0098000
  | 0, 3 => 0x1c646f31b346a71a0465b18d461617c05ca169057e154852c14184e0130449b11d444f10a44100fa83c40e783780d4831f0be42d30ab4287095022e08201e206bc189058c13d045c0f1032c0a501c804c0098000
  | 0, 4 => 0x1c746fe1b486a61a0065a18d060e17a05c21670576154052a14104d112ac485117c439104c3ed0f1c3a10db83480c882fc0b402aa0a1025e08fc21307b41c7068417b055412f04240ea02f809801c804c0098000
  | 0, 5 => 0x1db87421c586ea1af869819b064018685f417385a815f055d14c4505137c4b9124c467110441b0fbc3c90e583630cf43170bc42cb0ab0286098022d07e81d406b8188058813c04400ea031009e01c804c0098000
  | 0, 6 => 0x1e887721d0c7131ba86c11a4466818e060f177c5af15fc54f1498504136c4b8122045c10c04040f443a50dfc3590ccc3070ba02bc0a58270091021807c81cc0698180056813404200e2030c09701c404b007c000
  | 0, 7 => 0x20888001f447a21dcc74a1c846f81b246a019dc641182c5dc16d8587157853513fc4d6129c471112041f0fd83cd0e9037b0d483290c002d70a8427208f021307741b4062c15504b010303680a401ec05200a4000
  | 0, 8 => 0x21448281ffc7d31e747741d387181ba46bd1a5066518f061317905ae15e054f14984fd13504a511f045310743e70ec43820d303160bb42b70a3826508bc20607741b4062c15504b010303680b1022005f00a4000
  | 0, 9 => 0x1f947bc1e4c76a1d047181bbc6c61a74674192c61517bc5c0165c56e151451c13cc4ca126c47211244200fdc3c10e483700d043120b8c2ba0a4426808fc21607c01c1062c16204f011303900bb025405f00d8000
  | 0, 10 => 0x1ff07d61e807771d387181ba46c01a2866118e060f17a45b315f455414b84f8133049d11e045010843f90f503ac0e1c35f0cc03080b8c2ba0a1025b08b020307681b1062015904c010703780af023405e00bc000
  | 0, 11 => 0x1e807771d3871c1bcc6ca1a84678193c62617f45d41688579154052713f84d5129847a114842d10143e00ed438c0d8c33a0c442e80ac8289098c24108601ef071819d05d014b04700f303340a401ec05200a4000
  | 0, 12 => 0x1fdc7ce1e9477f1d247201bdc6ce1a9467c194c62a18045cb167056614f450413384a511f045310a84010f603af0e1835d0cd030e0b942af0a1825d08d020507701b3062816104e010f03980bd021c05800bc000
  | 0, 13 => 0x1ebc7861d747251bf06d31aa8681192c61c17cc5c1163c56614f451413ac4c21264470111c41e0fe03cf0e9837d0d5032e0c082dd0ad429009a023c08341e106c81860584142044c0eb02f009401c804d0094000
  | 0, 14 => 0x1ea47801d5c72e1c206df1ae4690199063f18685fb174c5a215e854b14704f4133049a11a044610783e80efc3960dc03470c782f50b302a309e825408ac20207701a605f414e04940fc034c0aa020405800bc000
  | 0, 15 => 0x1fe87d41e947831d5072b1c086d31a7466718f861517b05c3166856b150851913c04c1126046f111841d0fd03cb0e883790d403170b782a509cc24a08841f8073c19d0590148047c0f603340a701f804f00a4000
  | 1, 0 => 0x1fc07ca1e8477b1d1471c1bcc6ca1a84672192462017dc5ce167c577153c52013c44c2124c46b10f04140f943bd0e2c3690ce83120ba42c00a5c26e091421c07cc1ba064416804fc10903680a401ec05200a4000
  | 1, 1 => 0x1e687711d2071f1bd86cd1a5c66818fc61617b45c4166c572152452013dc4ce12b0483116843110203df0ed838d0d9033b0c482e90b0029709b824508701f307281a105e015c0498100035c0ae01e005200a4000
  | 1, 2 => 0x1e007571cb87051b706b31a2866118e060f17985bd165056b150851913c04c7127847511304230fe83d10ea03860d743340c2c2e20ae429009b824508701f307281a105ac14504700f603340a401ec05200a4000
  | 1, 3 => 0x1dc07471c786f51b306a319e865118a05ff17585ad161055b14c8509139c4be125446c110c41a0fc43c80e7c3760d343240bec2d20aa4280095c22e08141dc07001a705f815504b010303340a401ec05200a4000
  | 1, 4 => 0x1e1c75e1cd470c1b8c6ba1a4466818fc61617b45c4166c572152452013dc4ce129447c114c42a10043d80ebc3860d743340c2c2e20ae4290099c23e08541ec070c19a05c4148047c0f603340a401ec05200a4000
  | 1, 5 => 0x1ec07811d4872a1bec6c51a3c66718e060f17985bd165056b150851913c04c7127847511304230fe83d10ea037f0d5832d0c102db0ac8289098023708381e506f019305c4148047c0f603340a401ec05200a4000
  | 1, 6 => 0x20707f71f3c7a31dd073e1c606e21ab0687197c63018205e016c4589159053c145c4ef131c49f11e844b10543df0ec03840d7832f0c002d10a8827d094422207cc1c40678178054012103c80c3023405700a0000
  | 1, 7 => 0x1fc87ca1e947791d5072f1c286e41af869819a464318345d716a057c154052113ac4b5121845a10ac3f50f183a10dac3460c842f50b2429d09dc25108ac20507741b5063416704e011003680ab01f004d00a0000
  | 1, 8 => 0x1e207601cd47101bac6c31a6066918e861517b45c81674572152851b13b04c4127c477114842a10083dd0ee03930dac33c0c502e50af429509c0248088c1fb074c1ae0608153049c0f8033009d01d404d00a0000
  | 1, 9 => 0x1d6c7361c2c6df1ad0688198c63e18645f4173c5a415e455414a44fd13444ac121c45b10bc40a0f943b90e343610cf03100bac2bf0a68274093822808081dc06f419705c414c04900fc03500a501fc0500094000
  | 1, 10 => 0x1c6c6fc1b586b01a2866418f861817c85cc1698580156c53c141c4db12d448f11a444310743f70f443ab0e303660d343270c082e30af428a099023e08481ed07141a605d0148048c0f403380a801f005100b0000
  | 1, 11 => 0x1ce87151bc06cb1a94679193462717d05ce1688576154052a13dc4d112b0486118044110543ef0f2439d0de034c0cb43070b882b60a4026a091021107ac1c5067c179054c12d041c0db02d409001c404c0098000
  | 1, 12 => 0x1e547631cc47021b646a719e0646185c5e516e459415a053c14404e412e0492119844110703f70f603ac0e1835a0cd030f0ba82cb0a7c2790950228080c1d706ac18c058013a04380e202d809701c804c0098000
  | 1, 13 => 0x222885b20a47fa1f0478f1d7472e1bf06cd1a6c669190461917c45c9165c56c150451613b84c3126c470111441d0fb83bc0e4c3640cd43030b502a209c024708601ef06f418e057012d03d00c2024c06100c8000
  | 1, 14 => 0x210881a1fbc7b61e3475b1cc870a1b7c6ad1a0865a18bc60717705a315c454214404e112bc48611504250fcc3c10e643710d2431e0bb02c10a5826b090c21807c01c50668172052411a03a00bf024006100bc000
  | 1, 15 => 0x20007db1ecc7881d807351c186d41ac868d19a064018605ed171459a15a053f14404de12bc47d115042b0ff03ca0e8436f0d0030e0b7c2ad0a1025908b820607841bf065c16c051c11503980b4021405300a0000
  | 2, 0 => 0x1fbc7c41e547631d0471c1bd06c91a80677191461c17b45bb164855914a850213684ab120c45b10b040a0fac3bc0e503650cf430b0b802b50a0c25808b41fb07581b4060815704b010703600a601f805300ac000
  | 2, 1 => 0x1f407a51dcc74e1c8c6fa1b446a819d864b18805f7171459c15a8541143c4d612904721134428100c3e70f083930dac33c0c502f20b4c2ab0a0c25408b01fa073c19d05c814d04ac10003540a301e005300ac000
  | 2, 2 => 0x1f487a91e007571cb87051b706b31a2865f18b45fb17485a9160054e14944fc134c4a8123047311284210fd83cd0e6c3700d503220bdc2c50a6826f091021907b81bc062815804cc111037c0b4020805700c8000
  | 2, 3 => 0x1e5076c1d107151bcc6cb1a70674194862317d05cc16905821568532140c4d412944831178436101c3e20ee838b0d9833e0c582ee0afc290098423908441ef071c19f05c014804800f803400a8021805e00bc000
  | 2, 4 => 0x1f607af1e187571c846f81b3c6a619f465418ac60317505ac162856114e050913684b1122045f10d84070f603af0e183570cb83050b702b309f425408ac20207641b4063c16a04ec11303900b5021805700a0000
  | 2, 5 => 0x1dc47421c646f01b1c69e19d464c188c60717785b5163056314e851113a04b6123446b11084170fb03ca0e843820d643310c082da0ac828a09a023f08741f4072c1a205e4150049c0f803400a802000510088000
  | 2, 6 => 0x1ca47001b5c6a51a0c65a18f862517f05d316a8581156053614344e4130849011b844510703f30f283a10de03490c802fe0b702b30a2026608f421407ac1c2069817e057c13d04500f203240a001e005000a0000
  | 2, 7 => 0x1c006d71ad468c19b464b18b060a17ac5c916a8582154c52b14304e412d449611b844810a44010f483a30e103650cd83070b602b00a44269092822407f81d606dc18f05c014104600ef031809d01ec05200a4000
  | 2, 8 => 0x21a07e01d606e81a105fc15d04d011203d80d402e008f01b404b0088000
  | _, _ => 0
def thetaFuel : Nat := 6

def chunkWord (blocks : Nat → Nat → Nat) (width batch i : Nat) : Nat :=
  let b := i / batch
  (blocks (b / 16) (b % 16) >>> (width * (i % batch))) &&& (2^width - 1)

def thetaReg : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, i =>
    if i < 7 then thetaHot i else
    let c := chunkWord thetaRecipeBlocks 26 32 i
    let op := c &&& 3
    let a := (c >>> 2) &&& 4095
    if op = 3 then xs517.getD a 0
    else if op = 0 then thetaReg fuel a ^^^ q7
    else
      let x := thetaReg fuel a
      let y := thetaReg fuel (c >>> 14)
      if op = 1 then x &&& y else x ||| y

def thetaUnpack : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, word =>
    let token := word &&& 7
    if token < 7 then thetaReg thetaFuel token :: thetaUnpack n (word >>> 3)
    else if (word &&& 8) = 0 then
      thetaReg thetaFuel (7 + ((word >>> 4) &&& 31)) :: thetaUnpack n (word >>> 9)
    else thetaReg thetaFuel ((word >>> 4) &&& 4095) :: thetaUnpack n (word >>> 16)

def thetaState (i : Nat) : List Nat :=
  let b := i / 48
  let word := thetaStateBlocks (b / 16) (b % 16) >>> chunkWord thetaOffsetBlocks 14 48 i
  thetaUnpack (word &&& 15) (word >>> 4)

def thetaHash (salt : Nat) : List Nat → Nat
  | [] => 0
  | w :: ws =>
    let z := w % 1048573 + salt
    z * z * z % 1048573 + thetaHash salt ws

def thetaGroupBase (s : Nat) (need : Bool) : Nat := (thetaStateGroup s need).1
def thetaGroupCount (s : Nat) (need : Bool) : Nat := (thetaStateGroup s need).2.1

def thetaLookupExact (s : Nat) (need : Bool) (key : Nat) (ws : List Nat) : Bool :=
  let group := thetaStateGroup s need
  let d0 := group.2.2.1
  let dc := group.2.2.2.1
  let h0 := group.2.2.2.2.1
  let hc := group.2.2.2.2.2
  if thetaGroupCount s need = 0 then false else
    let d := chunkWord thetaShiftBlocks 13 64 (d0 + key % dc)
    let slot := chunkWord thetaSlotBlocks 12 64 (h0 + (thetaHash 193 ws + d) % hc)
    Nat.blt (slot-1) (thetaGroupCount s need) && Nat.blt 0 slot &&
      ws.isPerm (thetaState (thetaGroupBase s need + (slot-1)))

def preferOrientation (a b : Nat × Nat) : Nat × Nat := if a.2 ≤ b.2 then a else b

def thetaOrientation (ws : List Nat) : Nat × Nat :=
  let a := (0,thetaHash 317 ws)
  let b := (1,thetaHash 317 (q38 ws))
  let c := (2,thetaHash 317 (q37 ws))
  let d := (3,thetaHash 317 (q38 (q37 ws)))
  preferOrientation (preferOrientation a b) (preferOrientation c d)

def thetaLookup (s : Nat) (need : Bool) (ws : List Nat) : Bool :=
  let p := thetaOrientation ws
  thetaLookupExact s need p.2 (yd p.1 ws)

lemma thetaLookupExactSound {s need key ws} (h : thetaLookupExact s need key ws = true) :
    ∃ i < thetaGroupCount s need, ws.Perm (thetaState (thetaGroupBase s need + i)) := by
  unfold thetaLookupExact at h
  dsimp only at h
  split at h
  · contradiction
  · simp only [Bool.and_eq_true,Nat.blt_eq] at h
    exact ⟨_,h.1.1,List.isPerm_iff.1 h.2⟩

lemma thetaLookupSound {s m need ws} (h : thetaLookup s need ws = true)
    (hr : MarkedNatRun s m ws) :
    ∃ i < thetaGroupCount s need, MarkedNatRun s m (thetaState (thetaGroupBase s need + i)) := by
  obtain ⟨i,hi,hp⟩ := thetaLookupExactSound h
  exact ⟨i,hi,MarkedRun.perm hp (markedOrient (thetaOrientation ws).1 hr)⟩

def thetaNearTight (oneNotImpossible : List Nat → Bool) (k : Nat)
    (need : Bool) (zs : List Nat) : Bool :=
  (zs.length == k) && (need || !((rd zs &&& se) == se)) && oneNotImpossible zs

def thetaContinuation (oneNotImpossible : List Nat → Bool) (k : Nat)
    (need neg tight : Bool) (zs : List Nat) : Bool :=
  let nextNeed := need && !neg
  !(tight && (nextNeed || q0x zs)) && !thetaNearTight oneNotImpossible k nextNeed zs &&
    !thetaLookup k nextNeed zs

def thetaCheck (oneNotImpossible : List Nat → Bool) : Nat → Bool → Nat → Bool
  | 0, need, i => need || !(thetaState (thetaGroupBase 0 need + i) == [qe])
  | k+1, need, i =>
    !(vyMarked k (thetaState (thetaGroupBase (k+1) need + i)) (thetaContinuation oneNotImpossible k need))

lemma thetaCheck_step (oneNotImpossible : List Nat → Bool) (k : Nat) (need : Bool) (i : Nat) :
    thetaCheck oneNotImpossible (k+1) need i =
      !(vyMarked k (thetaState (thetaGroupBase (k+1) need + i)) (thetaContinuation oneNotImpossible k need)) := rfl

lemma thetaNeedFalse {b m : Bool} (hn : b = true → m = true) (hm : m = false) : b = false := by
  cases b <;> simp_all

set_option maxRecDepth 20000 in
lemma thetaCheckSound {oneNotImpossible : List Nat → Bool}
    (hsound : ∀ {k zs}, MarkedNatRun k true zs → zs.length = k → oneNotImpossible zs = false)
    (hc : ∀ s ≤ 11, ∀ need, ∀ i < thetaGroupCount s need, thetaCheck oneNotImpossible s need i = true) :
    ∀ s ≤ 11, ∀ need, ∀ i < thetaGroupCount s need, ∀ m,
      (need = true → m = true) → ¬ MarkedNatRun s m (thetaState (thetaGroupBase s need + i)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs need i hi m hm hrun
    have hchk := hc s hs need i hi
    cases s with
    | zero =>
      have hz : thetaGroupCount 0 need = 0 := by cases need <;> rfl
      omega
    | succ k =>
      have hf (neg mark : Bool) (zs : List Nat) (hmk : m = (neg || mark))
          (hz : MarkedNatRun k mark zs) :
          thetaContinuation oneNotImpossible k need neg (decide (zs.length = k+1)) zs = true := by
        have hn : (need && !neg) = true → mark = true := by
          cases need <;> cases neg <;> cases mark <;> simp_all
        have hd : thetaLookup k (need && !neg) zs = false := by
          cases eq : thetaLookup k (need && !neg) zs
          · rfl
          · obtain ⟨j,hj,hz'⟩ := thetaLookupSound eq hz
            exact (ih k (by omega) (by omega) _ j hj mark hn hz').elim
        have htight : (decide (zs.length = k+1) && ((need && !neg) || q0x zs)) = false := by
          by_cases ht : zs.length = k+1
          · rw [decide_eq_true ht,thetaNeedFalse hn (MarkedRun.tight hz ht),q1n (MarkedRun.forget hz) ht] <;> rfl
          · simp [ht]
        have hnear : thetaNearTight oneNotImpossible k (need && !neg) zs = false := by
          by_cases ht : zs.length = k
          · cases mark
            · have hd' := markedMonotoneCover hz
              have hnext := thetaNeedFalse hn rfl
              simp [thetaNearTight,ht,hd',hnext]
            · simp [thetaNearTight,hsound hz ht]
          · simp [thetaNearTight,ht]
        simp only [thetaContinuation]
        rw [htight,hnear,hd] <;> rfl
      have h := markedStep hrun k rfl _ (List.Perm.refl _) (thetaContinuation oneNotImpossible k need) hf
      have hnone := (thetaCheck_step oneNotImpossible k need i).symm.trans hchk
      exact Bool.false_ne_true ((congrArg Bool.not h).symm.trans hnone)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_0_0 : span (thetaCheck thetaOneNotFast 6 true) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_1_0 : span (thetaCheck thetaOneNotFast 7 false) 64 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_1_1 : span (thetaCheck thetaOneNotFast 7 false) 64 64 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_1_2 : span (thetaCheck thetaOneNotFast 7 false) 64 128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_1_3 : span (thetaCheck thetaOneNotFast 7 false) 64 192 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_1_4 : span (thetaCheck thetaOneNotFast 7 false) 58 256 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_2_0 : span (thetaCheck thetaOneNotFast 7 true) 20 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_0 : span (thetaCheck thetaOneNotFast 8 false) 64 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_1 : span (thetaCheck thetaOneNotFast 8 false) 64 64 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_2 : span (thetaCheck thetaOneNotFast 8 false) 64 128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_3 : span (thetaCheck thetaOneNotFast 8 false) 64 192 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_4 : span (thetaCheck thetaOneNotFast 8 false) 64 256 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_5 : span (thetaCheck thetaOneNotFast 8 false) 64 320 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_6 : span (thetaCheck thetaOneNotFast 8 false) 64 384 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_7 : span (thetaCheck thetaOneNotFast 8 false) 64 448 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_8 : span (thetaCheck thetaOneNotFast 8 false) 64 512 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_9 : span (thetaCheck thetaOneNotFast 8 false) 64 576 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_10 : span (thetaCheck thetaOneNotFast 8 false) 64 640 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_11 : span (thetaCheck thetaOneNotFast 8 false) 64 704 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_12 : span (thetaCheck thetaOneNotFast 8 false) 64 768 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_13 : span (thetaCheck thetaOneNotFast 8 false) 64 832 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_3_14 : span (thetaCheck thetaOneNotFast 8 false) 20 896 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_4_0 : span (thetaCheck thetaOneNotFast 8 true) 64 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_4_1 : span (thetaCheck thetaOneNotFast 8 true) 64 64 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_4_2 : span (thetaCheck thetaOneNotFast 8 true) 3 128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_5_0 : span (thetaCheck thetaOneNotFast 9 false) 64 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_5_1 : span (thetaCheck thetaOneNotFast 9 false) 64 64 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_5_2 : span (thetaCheck thetaOneNotFast 9 false) 64 128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_5_3 : span (thetaCheck thetaOneNotFast 9 false) 64 192 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_5_4 : span (thetaCheck thetaOneNotFast 9 false) 64 256 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_5_5 : span (thetaCheck thetaOneNotFast 9 false) 37 320 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_6_0 : span (thetaCheck thetaOneNotFast 9 true) 64 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_6_1 : span (thetaCheck thetaOneNotFast 9 true) 64 64 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_6_2 : span (thetaCheck thetaOneNotFast 9 true) 43 128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_7_0 : span (thetaCheck thetaOneNotFast 10 false) 6 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_8_0 : span (thetaCheck thetaOneNotFast 10 true) 20 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaSpan_9_0 : span (thetaCheck thetaOneNotFast 11 true) 1 0 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma allThetaChecks :

    ∀ s ≤ 11, ∀ need, ∀ i < thetaGroupCount s need, thetaCheck thetaOneNotFast s need i = true := by
  intro s hs need i hi
  interval_cases s <;> cases need <;>
    simp only [thetaGroupCount,thetaStateGroup,Nat.not_lt_zero] at hi
  · exact span_ok thetaSpan_0_0 i (by omega) (by omega)
  · by_cases ht0 : i < 64
    · exact span_ok thetaSpan_1_0 i (by omega) (by omega)
    · by_cases ht1 : i < 128
      · exact span_ok thetaSpan_1_1 i (by omega) (by omega)
      · by_cases ht2 : i < 192
        · exact span_ok thetaSpan_1_2 i (by omega) (by omega)
        · by_cases ht3 : i < 256
          · exact span_ok thetaSpan_1_3 i (by omega) (by omega)
          · exact span_ok thetaSpan_1_4 i (by omega) (by omega)
  · exact span_ok thetaSpan_2_0 i (by omega) (by omega)
  · by_cases ht0 : i < 64
    · exact span_ok thetaSpan_3_0 i (by omega) (by omega)
    · by_cases ht1 : i < 128
      · exact span_ok thetaSpan_3_1 i (by omega) (by omega)
      · by_cases ht2 : i < 192
        · exact span_ok thetaSpan_3_2 i (by omega) (by omega)
        · by_cases ht3 : i < 256
          · exact span_ok thetaSpan_3_3 i (by omega) (by omega)
          · by_cases ht4 : i < 320
            · exact span_ok thetaSpan_3_4 i (by omega) (by omega)
            · by_cases ht5 : i < 384
              · exact span_ok thetaSpan_3_5 i (by omega) (by omega)
              · by_cases ht6 : i < 448
                · exact span_ok thetaSpan_3_6 i (by omega) (by omega)
                · by_cases ht7 : i < 512
                  · exact span_ok thetaSpan_3_7 i (by omega) (by omega)
                  · by_cases ht8 : i < 576
                    · exact span_ok thetaSpan_3_8 i (by omega) (by omega)
                    · by_cases ht9 : i < 640
                      · exact span_ok thetaSpan_3_9 i (by omega) (by omega)
                      · by_cases ht10 : i < 704
                        · exact span_ok thetaSpan_3_10 i (by omega) (by omega)
                        · by_cases ht11 : i < 768
                          · exact span_ok thetaSpan_3_11 i (by omega) (by omega)
                          · by_cases ht12 : i < 832
                            · exact span_ok thetaSpan_3_12 i (by omega) (by omega)
                            · by_cases ht13 : i < 896
                              · exact span_ok thetaSpan_3_13 i (by omega) (by omega)
                              · exact span_ok thetaSpan_3_14 i (by omega) (by omega)
  · by_cases ht0 : i < 64
    · exact span_ok thetaSpan_4_0 i (by omega) (by omega)
    · by_cases ht1 : i < 128
      · exact span_ok thetaSpan_4_1 i (by omega) (by omega)
      · exact span_ok thetaSpan_4_2 i (by omega) (by omega)
  · by_cases ht0 : i < 64
    · exact span_ok thetaSpan_5_0 i (by omega) (by omega)
    · by_cases ht1 : i < 128
      · exact span_ok thetaSpan_5_1 i (by omega) (by omega)
      · by_cases ht2 : i < 192
        · exact span_ok thetaSpan_5_2 i (by omega) (by omega)
        · by_cases ht3 : i < 256
          · exact span_ok thetaSpan_5_3 i (by omega) (by omega)
          · by_cases ht4 : i < 320
            · exact span_ok thetaSpan_5_4 i (by omega) (by omega)
            · exact span_ok thetaSpan_5_5 i (by omega) (by omega)
  · by_cases ht0 : i < 64
    · exact span_ok thetaSpan_6_0 i (by omega) (by omega)
    · by_cases ht1 : i < 128
      · exact span_ok thetaSpan_6_1 i (by omega) (by omega)
      · exact span_ok thetaSpan_6_2 i (by omega) (by omega)
  · exact span_ok thetaSpan_7_0 i (by omega) (by omega)
  · exact span_ok thetaSpan_8_0 i (by omega) (by omega)
  · exact span_ok thetaSpan_9_0 i (by omega) (by omega)

lemma thetaRootLookup : thetaLookup 11 true xs517 = true := by decide +kernel

theorem thetaNoNot11 : ¬ MarkedNatRun 11 true xs517 := by
  intro h
  obtain ⟨i,hi,hs⟩ := thetaLookupSound thetaRootLookup h
  exact thetaCheckSound thetaOneNotFast_false allThetaChecks 11 (by decide) true i hi true (fun _ => rfl) hs

end Theta
abbrev q0:=Nat × Nat
def rx : Nat:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def rm (x : Nat) : Nat:=x^^^rx
def rv : q0:=(0,0)
def v5 : q0:=(rx,rx)
def qc : q0:=(rx,0)
def qx (a : q0) : q0:=(rm a.1,rm a.2)
def qn (isOr : Bool) (a b : q0) : q0 :=
  if isOr then (a.1|||b.1,a.2|||b.2) else (a.1&&&b.1,a.2&&&b.2)
def qr (x : Nat) : Prop:=∀ j,252 ≤ j->x.testBit j=false
def qb (a : q0) : Prop:=qr a.1/\qr a.2
def qd (a : q0) : Prop:=qb a/\a ≠ rv/\a ≠ v5
def x3 : q0:=(0x988c662c60004200118004e25321040016c0030d9e4a00039fffd8007000fff,0x988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712)
def q1d : q0:=(0x2130860080010c00060007c01c3e180027000332607ffff2640020007ffffff,0x2130840090850d0886422180040e1a2125221210201110d226222444488a88c)
def q1c : q0:=(0xf88f000070001800070463c0200039fffcc3878c001c78003fff9fff000,0x288f043070431810c6040140208600486843828c4604588c09191234230)
def yv : q0:=(0xc03f0130000180001ffff8387c07c0003e0000fc07f0001f80003fffe000000,0xc015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8)
def q1b : q0:=(0x1c001c00001ffffe000003f8007ffffc00000fff800001fffffc0000000000,0x1c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068)
def yu : q0:=(0xfe0001fffffe00000000003ffff80000000000ffffffffe0000000000000000,0xca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170)
def yt : q0:=(0xfffffe00000000000000003fffffffffffffff0000000000000000000000000,0xffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80)
def q1a : q0:=(0xffffffffffffffffffffffc0000000000000000000000000000000000000000,0x35eafe0ade006be01d7807c000000380003800000001c000038007000e00e00)
def rj : List q0:=[x3,q1d,q1c,yv,q1b,yu,yt,q1a]
lemma y6 : rx=2 ^ 252 - 1:= by
  have h1 : rx=2 ^ 126*2 ^ 126 - 1:= by decide
  rw [h1,← Nat.pow_add]
lemma qg (j : Nat) : rx.testBit j=decide (j<252):= by
  rw [y6];exact Nat.testBit_two_pow_sub_one 252 j
lemma uw {x : Nat} (hx : qr x) (j : Nat) :
    (rm x).testBit j=if j<252 then !(x.testBit j) else false:= by
  simp only [rm,Nat.testBit_xor,qg]
  by_cases hj : j<252
  · simp [hj]
  · simp [hj,hx j (by omega)]
lemma q5 (x : Nat) {j : Nat} (hj : j<252) :
    (rm x).testBit j=!(x.testBit j):= by
  simp [rm,Nat.testBit_xor,qg,hj]
lemma sc : qr 0:=fun _ _=>Nat.zero_testBit _
lemma vh : qr rx:=fun j hj=>by
  rw [qg];simp [show ¬ j<252 by omega]
lemma xm {x : Nat} (hx : qr x) : qr (rm x):=fun j hj=>by
  rw [uw hx];simp [show ¬ j<252 by omega]
lemma s4 {x y : Nat} (hx : qr x) : qr (x&&&y):=fun j hj=>by
  rw [Nat.testBit_and,hx j hj];rfl
lemma uz {x y : Nat} (hx : qr x) (hy : qr y) : qr (x|||y):=fun j hj=>by
  rw [Nat.testBit_or,hx j hj,hy j hj];rfl
lemma q0s {x y : Nat} (hx : qr x) (hy : qr y) : qr (x^^^y):=fun j hj=>by
  rw [Nat.testBit_xor,hx j hj,hy j hj];rfl
lemma uj {x : Nat} (h : x ≤ rx) : qr x:=fun j hj=>by
  have hlt : x<2 ^ 252:= by
    have hp : 0<2 ^ 252:=Nat.pow_pos (by omega)
    rw [y6] at h;omega
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hj))
lemma vg : qb rv:=⟨sc,sc⟩
lemma q0r : qb v5:=⟨vh,vh⟩
lemma z3 : qb qc:=⟨vh,sc⟩
lemma ye {a : q0} (ha : qb a) : qb (qx a) :=
  ⟨xm ha.1,xm ha.2⟩
lemma x9 (d : Bool) {a b : q0} (ha : qb a) (hb : qb b) :
    qb (qn d a b):= by
  cases d
  · exact ⟨s4 ha.1,s4 ha.2⟩
  · exact ⟨uz ha.1 hb.1,uz ha.2 hb.2⟩
lemma s0 (d : Bool) (a b : q0) : qn d a b=qn d b a:= by
  cases d <;> simp [qn,Nat.and_comm,Nat.or_comm]
lemma so {a : q0} (ha : qb a) :
    qn false a v5=a/\qn true a rv=a ∧
    qn false a rv=rv/\qn true a v5=v5 ∧
    qn false a a=a/\qn true a a=a:= by
  obtain ⟨p,n⟩:=a
  have hp1 : p&&&rx=p:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_and,qg];by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.1 j (by omega)]
  have hn1 : n&&&rx=n:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_and,qg];by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.2 j (by omega)]
  have hp2 : p|||rx=rx:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_or,qg];by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.1 j (by omega)]
  have hn2 : n|||rx=rx:=Nat.eq_of_testBit_eq fun j=>by
    rw [Nat.testBit_or,qg];by_cases hj : j<252
    · simp [hj]
    · simp [hj,ha.2 j (by omega)]
  simp [qn,v5,rv,hp1,hn1,hp2,hn2]
lemma v6 : qx rv=v5/\qx v5=rv:= by
  constructor
  · simp [qx,rv,v5,rm]
  · simp [qx,rv,v5,rm]
def y7 (a : Sig) : q0:=(a.1.toNat,a.2.toNat)
lemma xb (x : B) : qr x.toNat:=fun j hj=>by
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) hj))
lemma q1h (a : Sig) : qb (y7 a):=⟨xb a.1,xb a.2⟩
lemma xn : Function.Injective y7:= by
  intro a b h
  have h1 : a.1.toNat=b.1.toNat:=congrArg Prod.fst h
  have h2 : a.2.toNat=b.2.toNat:=congrArg Prod.snd h
  exact Prod.ext (BitVec.eq_of_toNat_eq h1) (BitVec.eq_of_toNat_eq h2)
lemma q28 : y7 zero=rv:=rfl
lemma q2y : y7 one=v5:= by
  apply Prod.ext <;> exact (by decide : (BitVec.allOnes 252).toNat=rx)
lemma q0t : y7 target=qc:= by
  apply Prod.ext
  · exact (by decide : (BitVec.allOnes 252).toNat=rx)
  · rfl
lemma q13 (a : Sig) : y7 (neg a)=qx (y7 a):= by
  have hnot (x : B) : (~~~x).toNat=rm x.toNat:= by
    apply Nat.eq_of_testBit_eq;intro j
    rw [BitVec.testBit_toNat,BitVec.getLsbD_not,uw (xb x)]
    by_cases hj : j<252
    · simp [hj,BitVec.testBit_toNat]
    · simp [hj]
  exact Prod.ext (hnot a.1) (hnot a.2)
lemma q14 (d : Bool) (a b : Sig) : y7 (bin d a b)=qn d (y7 a) (y7 b):= by
  cases d <;> simp [bin,qn,y7]
lemma xc {a : Sig} (ha : proper a) : qd (y7 a):= by
  refine ⟨q1h a,fun h=>ha.1 (xn (h.trans q28.symm)),
    fun h=>ha.2 (xn (h.trans q2y.symm))⟩
def qy  (k t : Nat) (S : Finset q0) : Prop :=
  ∀ (P : Nat → Nat → Finset q0 → Prop),(P 0 0 {qc}) →
    (∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hfresh : qx a ∉ insert a U) (ih : P k t (insert (qx a) U)),P (k+1) (t+1) (insert a U)) →
    (∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hfresh : qn d a b ∉ insert a (insert b U)) (ih : P k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U))) → P k t S
theorem qy.stop   : qy 0 0 {qc}:=by
  intro P stop unary binary
  exact @stop
theorem qy.unary  {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hfresh : qx a ∉ insert a U) (tail : qy k t (insert (qx a) U)) : qy (k+1) (t+1) (insert a U):=by
  intro P stop unary binary
  exact @unary k t U a ha hfresh (tail P stop unary binary)
theorem qy.binary  {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hfresh : qn d a b ∉ insert a (insert b U)) (tail : qy k t (insert (qn d a b) U)) : qy (k+1) t (insert a (insert b U)):=by
  intro P stop unary binary
  exact @binary k t U a b d ha hb hab hfresh (tail P stop unary binary)
theorem qy.elimInd  {P : Nat → Nat → Finset q0 → Prop}
    (stop : P 0 0 {qc})
    (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hfresh : qx a ∉ insert a U) (tail : qy k t (insert (qx a) U)) (ih : P k t (insert (qx a) U)),P (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hfresh : qn d a b ∉ insert a (insert b U)) (tail : qy k t (insert (qn d a b) U)) (ih : P k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U))) {k t : Nat} {S : Finset q0} (h : qy k t S) : P k t S:=by
  apply And.right (a:=qy k t S)
  apply h (fun k t S=>qy k t S ∧ P k t S)
  · exact ⟨@qy.stop  ,@stop  ⟩
  · intro k t U a ha hfresh prev
    exact ⟨@qy.unary k t U a ha hfresh prev.1,@unary k t U a ha hfresh prev.1 prev.2⟩
  · intro k t U a b d ha hb hab hfresh prev
    exact ⟨@qy.binary k t U a b d ha hb hab hfresh prev.1,@binary k t U a b d ha hb hab hfresh prev.1 prev.2⟩
theorem qy.elimCases  {P : Nat → Nat → Finset q0 → Prop}
    (stop : P 0 0 {qc})
    (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hfresh : qx a ∉ insert a U) (tail : qy k t (insert (qx a) U)),P (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hfresh : qn d a b ∉ insert a (insert b U)) (tail : qy k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U))) {k t : Nat} {S : Finset q0} (h : qy k t S) : P k t S:=by
  apply qy.elimInd (P:=P) (h:=h)
  · exact @stop
  · intro k t U a ha hfresh prev ih
    exact @unary k t U a ha hfresh prev
  · intro k t U a b d ha hb hab hfresh prev ih
    exact @binary k t U a b d ha hb hab hfresh prev
theorem qy.byInd  {P : ∀ (k t : Nat) (S : Finset q0),qy k t S → Prop}
  (stop : P 0 0 {qc} (@qy.stop ))
  (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hfresh : qx a ∉ insert a U) (tail : qy k t (insert (qx a) U)) (ih : P k t (insert (qx a) U) tail),P (k+1) (t+1) (insert a U) (@qy.unary k t U a ha hfresh tail))
  (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hfresh : qn d a b ∉ insert a (insert b U)) (tail : qy k t (insert (qn d a b) U)) (ih : P k t (insert (qn d a b) U) tail),P (k+1) t (insert a (insert b U)) (@qy.binary k t U a b d ha hb hab hfresh tail)) {k t : Nat} {S : Finset q0} (h : qy k t S) : P k t S h:=by
  have aux : ∀ hx : qy k t S,P k t S hx:=by
    apply qy.elimInd (P:=fun k t S=>∀ hx : qy k t S,P k t S hx) (h:=h)
    · intro  hx
      exact @stop
    · intro k t U a ha hfresh prev ih hx
      exact @unary k t U a ha hfresh prev (ih prev)
    · intro k t U a b d ha hb hab hfresh prev ih hx
      exact @binary k t U a b d ha hb hab hfresh prev (ih prev)
  exact aux h
theorem qy.byCases  {P : ∀ (k t : Nat) (S : Finset q0),qy k t S → Prop}
  (stop : P 0 0 {qc} (@qy.stop ))
  (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hfresh : qx a ∉ insert a U) (tail : qy k t (insert (qx a) U)),P (k+1) (t+1) (insert a U) (@qy.unary k t U a ha hfresh tail))
  (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hfresh : qn d a b ∉ insert a (insert b U)) (tail : qy k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U)) (@qy.binary k t U a b d ha hb hab hfresh tail)) {k t : Nat} {S : Finset q0} (h : qy k t S) : P k t S h:=by
  have aux : ∀ hx : qy k t S,P k t S hx:=by
    apply qy.elimCases (P:=fun k t S=>∀ hx : qy k t S,P k t S hx) (h:=h)
    · intro  hx
      exact @stop
    · intro k t U a ha hfresh prev hx
      exact @unary k t U a ha hfresh prev
    · intro k t U a b d ha hb hab hfresh prev hx
      exact @binary k t U a b d ha hb hab hfresh prev
  exact aux h
lemma z5 {k t : Nat} {S : Finset Sig} (h : Live k t S) :
    qy k t (S.image y7):= by
  induction h using Live.byInd with
  | stop=>simpa [q0t] using qy.stop
  | @unary k t U a ha hf _ ih =>
    simp only [Finset.image_insert,q13] at ih ⊢
    have hf' : qx (y7 a) ∉ insert (y7 a) (U.image y7):= by
      rw [← Finset.image_insert,← q13]
      intro hx;obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      exact hf (xn he ▸ hy)
    exact qy.unary (xc ha) hf' ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    simp only [Finset.image_insert,q14] at ih ⊢
    have hf' : qn d (y7 a) (y7 b) ∉ insert (y7 a) (insert (y7 b) (U.image y7)):= by
      rw [← Finset.image_insert,← Finset.image_insert,← q14]
      intro hx;obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      exact hf (xn he ▸ hy)
    exact qy.binary (xc ha) (xc hb) (fun e=>hab (xn e)) hf' ih
lemma q00 {a : Sig} (ha : a ∈ raw) : y7 a ∈ rj:= by
  have h : raw.map y7=rj:= by decide +kernel
  rw [← h];exact List.mem_map_of_mem ha
def r9 (d : Bool) (a : q0) : Nat :=
  if d then a.1^^^a.2 else a.1&&&rm a.2
def q9 (d : Bool) : List q0->Nat
  | []=>0
  | a :: l=>r9 d a|||q9 d l
def rg (a b : q0) : Bool:=Nat.beq a.1 b.1&&Nat.beq a.2 b.2
lemma rf (a b : q0) : rg a b=true ↔ a=b:= by
  cases a;cases b;simp only [rg,Bool.and_eq_true,Nat.beq_eq,Prod.mk.injEq]
def up (x : q0) : List q0->Bool
  | []=>false
  | y :: ys=>rg x y||up x ys
lemma y5 (x : q0) (l : List q0) : up x l=true ↔ x ∈ l:= by
  induction l with
  | nil=>simp [up]
  | cons y ys ih=>simp [up,rf,ih]
def v4 : List q0->Bool
  | []=>true
  | x :: xs=>!up x xs&&v4 xs
lemma ve {l : List q0} (h : v4 l=true) : l.Nodup:= by
  induction l with
  | nil=>exact List.nodup_nil
  | cons x xs ih =>
    simp only [v4,Bool.and_eq_true,Bool.not_eq_true'] at h
    exact List.nodup_cons.mpr ⟨fun hm=>by rw [(y5 x xs).mpr hm] at h;exact Bool.false_ne_true h.1.symm,ih h.2⟩
def sn (x : q0) : List q0->Option (List q0)
  | []=>none
  | y :: ys=>if rg x y then some ys else
    match sn x ys with | none=>none | some r=>some (y :: r)
lemma yq {x : q0} {ys r : List q0} (h : sn x ys=some r) :
    ys.Perm (x :: r):= by
  induction ys generalizing r with
  | nil=>simp [sn] at h
  | cons y ys ih =>
    simp only [sn] at h
    cases he : rg x y
    · rw [he] at h
      cases hr : sn x ys with
      | none=>rw [hr] at h;contradiction
      | some r' =>
        rw [hr] at h;injection h with h;subst h
        exact ((ih hr).cons y).trans (List.Perm.swap _ _ _)
    · rw [he] at h;injection h with h;subst h
      rw [(rf x y).mp he]
def vp : List q0->List q0->Bool
  | [],[]=>true
  | x :: xs,ys=>match sn x ys with | none=>false | some ys'=>vp xs ys'
  | _,_=>false
lemma yp {xs ys : List q0} (h : vp xs ys=true) : xs.Perm ys:= by
  induction xs generalizing ys with
  | nil=>cases ys with | nil=>exact List.Perm.nil | cons _ _=>simp [vp] at h
  | cons x xs ih =>
    simp only [vp] at h
    cases he : sn x ys with
    | none=>rw [he] at h;contradiction
    | some ys'=>rw [he] at h;exact ((ih h).cons x).trans (yq he).symm
def qw (del v : List q0) : List q0:=v.filter (fun x=>!(del.contains x))
def vs (a : q0) : List q0->List q0
  | []=>[]
  | x :: xs=>if rg a x then vs a xs else x :: vs a xs
def ug (a b : q0) : List q0->List q0
  | []=>[]
  | x :: xs=>if rg a x||rg b x then ug a b xs else x :: ug a b xs
lemma q0h (a : q0) (v : List q0) : vs a v=qw [a] v:= by
  induction v with
  | nil=>rfl
  | cons x xs ih =>
    simp only [vs,qw,List.filter_cons,List.contains_eq_mem,List.mem_singleton] at ih ⊢
    by_cases h : a=x
    · subst h;rw [(rf a a).mpr rfl];simp [ih]
    · have hf : rg a x=false:= by cases he : rg a x;rfl;exact (h ((rf a x).mp he)).elim
      have hne : decide (x=a)=false:=decide_eq_false (Ne.symm h)
      rw [hf,hne];simp [ih]
lemma q0g (a b : q0) (v : List q0) : ug a b v=qw [a,b] v:= by
  induction v with
  | nil=>rfl
  | cons x xs ih =>
    simp only [ug,qw,List.filter_cons,List.contains_eq_mem,List.mem_cons,List.not_mem_nil,or_false] at ih ⊢
    by_cases h : a=x\/b=x
    · have ht : (rg a x||rg b x)=true:= by
        rcases h with rfl | rfl <;> simp [(rf _ _).mpr rfl]
      have hm : decide (x=a\/x=b)=true:=decide_eq_true (by rcases h with rfl | rfl <;> simp)
      rw [ht,hm];simp [ih]
    · have ha : a ≠ x:=fun e=>h (Or.inl e)
      have hb : b ≠ x:=fun e=>h (Or.inr e)
      have hfa : rg a x=false:= by cases he : rg a x;rfl;exact (ha ((rf a x).mp he)).elim
      have hfb : rg b x=false:= by cases he : rg b x;rfl;exact (hb ((rf b x).mp he)).elim
      have hm : decide (x=a\/x=b)=false:=decide_eq_false (by rintro (rfl | rfl);exact ha rfl;exact hb rfl)
      rw [hfa,hfb,hm];simp [ih]
abbrev y3:=Nat × Nat × Nat
def r0 (z : Nat) (c : y3) : y3 :=
  let nz:=rm z
  (z|||c.1,(z&&&rm c.1)|||(c.2.1&&&nz),
   (z&&&c.2.1)|||(c.2.2&&&nz))
def qz (d : Bool) : List q0->y3
  | []=>(0,0,0)
  | a :: l=>r0 (r9 d a) (qz d l)
def q0a (z : Nat) (c : Nat × Nat) : Nat × Nat :=
  (z|||c.1,(z&&&rm c.1)|||(c.2&&&rm z))
def zi : List q0->Nat × Nat
  | []=>(0,0)
  | a :: l=>q0a (r9 false a) (zi l)
lemma q2c (v : List q0) :
    (zi v).1=(qz false v).1/\(zi v).2=(qz false v).2.1:= by
  induction v with
  | nil=>exact ⟨rfl,rfl⟩
  | cons a l ih=>simp only [zi,qz,q0a,r0,ih.1,ih.2,and_self]
def vr (c : y3) (a : Nat) : Nat:=c.1&&&rm (c.2.1&&&a)
def uc (c : y3) (a b : Nat) : Nat :=
  c.1&&&rm ((c.2.1&&&(a|||b))|||(c.2.2&&&(a&&&b)))
def sv (c : y3) : Prop:=qr c.1/\qr c.2.1/\qr c.2.2
lemma rq (d : Bool) {a : q0} (ha : qb a) : qr (r9 d a):= by
  cases d
  · exact s4 ha.1
  · exact q0s ha.1 ha.2
lemma zl {z : Nat} {c : y3} (hz : qr z) (hc : sv c) :
    sv (r0 z c) :=
  ⟨uz hz hc.1,uz (s4 hz) (s4 hc.2.1),
   uz (s4 hz) (s4 hc.2.2)⟩
lemma ru (d : Bool) {v : List q0} (hv : ∀ a ∈ v,qb a) :
    sv (qz d v):= by
  induction v with
  | nil=>exact ⟨sc,sc,sc⟩
  | cons a l ih =>
    exact zl (rq d (hv a List.mem_cons_self))
      (ih fun b hb=>hv b (List.mem_cons_of_mem _ hb))
lemma q33 {c : y3} {a : Nat} (hc : sv c) (ha : qr a) :
    vr (r0 a c) a=c.1:= by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases hi : i<252
  · simp only [vr,r0,Nat.testBit_or,Nat.testBit_and,q5 _ hi]
    cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
  · have hge : 252 ≤ i:= by omega
    simp [vr,r0,Nat.testBit_and,Nat.testBit_or,ha i hge,hc.1 i hge]
lemma q32 {c : y3} {a b : Nat} (hc : sv c) (ha : qr a) (hb : qr b) :
    uc (r0 a (r0 b c)) a b=c.1:= by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases hi : i<252
  · simp only [uc,r0,Nat.testBit_or,Nat.testBit_and,q5 _ hi]
    cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
  · have hge : 252 ≤ i:= by omega
    simp [uc,r0,Nat.testBit_and,Nat.testBit_or,ha i hge,hb i hge,hc.1 i hge]
lemma zq {c : y3} {a b : Nat} (hc : sv c) (ha : qr a) (hb : qr b) :
    r0 a (r0 b c)=r0 b (r0 a c):= by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq;intro i
    simp only [r0,Nat.testBit_or]
    cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> (apply Nat.eq_of_testBit_eq;intro i;by_cases hi : i<252)
    · simp only [r0,Nat.testBit_or,Nat.testBit_and,q5 _ hi]
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
        cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
    · have hge : 252 ≤ i:= by omega
      simp [r0,Nat.testBit_and,Nat.testBit_or,ha i hge,hb i hge,hc.2.1 i hge]
    · simp only [r0,Nat.testBit_or,Nat.testBit_and,q5 _ hi]
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
        cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
    · have hge : 252 ≤ i:= by omega
      simp [r0,Nat.testBit_and,Nat.testBit_or,ha i hge,hb i hge,hc.2.2 i hge]
lemma q0i (d : Bool) {l r : List q0} (h : l.Perm r) (hl : ∀ a ∈ l,qb a) :
    qz d l=qz d r:= by
  induction h with
  | nil=>rfl
  | cons a _ ih =>
    exact congrArg (r0 (r9 d a)) (ih fun x hx=>hl x (List.mem_cons_of_mem _ hx))
  | @swap a b t =>
    exact zq (ru d fun x hx=>hl x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
      (rq d (hl b (List.mem_cons_self)))
      (rq d (hl a (List.mem_cons_of_mem _ List.mem_cons_self)))
  | trans p _ h1 h2=>exact (h1 hl).trans (h2 fun x hx=>hl x (p.mem_iff.mpr hx))
lemma zj (d : Bool) (v : List q0) : (qz d v).1=q9 d v:= by
  induction v with
  | nil=>rfl
  | cons a v ih=>change r9 d a|||(qz d v).1=r9 d a|||q9 d v;rw [ih]
lemma vq : qd qc:=⟨z3,by decide,by decide⟩
lemma qv {k t S} (h : qy k t S) : ∀ a ∈ S,qd a:= by
  induction h using qy.byInd with
  | stop=>simpa using vq
  | unary ha _ _ ih=>simpa using And.intro ha (fun a h=>ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h=>ih a (Finset.mem_insert_of_mem h)⟩
lemma xg {k t S} (h : qy k t S) : t ≤ k/\S.card+t ≤ k+1:= by
  induction h using qy.byInd with
  | stop=>simp
  | @unary k t U a _ hf _ ih =>
    have hu : qx a ∉ U:=fun hm=>hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc:=Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d _ _ _ hf _ ih =>
    have hu : qn d a b ∉ U:=fun hm=>hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1:=Finset.card_insert_le (a:=a) (s:=insert b U)
    have h2:=Finset.card_insert_le (a:=b) (s:=U)
    exact ⟨by omega,by omega⟩
lemma q1i (t : Nat) (a : q0) (i : Nat) (hi : i<252)
    (h : (r9 (decide (0<t)) (qx a)).testBit i=true) :
    (r9 true a).testBit i=true:= by
  cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> cases ht : decide (0<t) <;>
    simp only [r9,qx,ite_true,ite_false,Bool.false_eq_true,Nat.testBit_xor,Nat.testBit_and,
      q5 _ hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide
lemma q0u (t d : Bool) (a b : q0) (i : Nat) (hi : i<252)
    (h : (r9 t (qn d a b)).testBit i=true) :
    (r9 t a).testBit i=true\/(r9 t b).testBit i=true:= by
  cases t <;> cases d <;>
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;>
    cases hu : b.1.testBit i <;> cases hv : b.2.testBit i <;>
    simp only [r9,qn,ite_true,ite_false,Bool.false_eq_true,Nat.testBit_xor,Nat.testBit_or,
      Nat.testBit_and,q5 _ hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide
lemma yj (t : Nat) (a : q0) (i : Nat) (hi : i<252)
    (h : (r9 (decide (0<t)) a).testBit i=true) : (r9 true a).testBit i=true:= by
  cases ht : decide (0<t) <;> cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;>
    simp only [r9,ite_true,ite_false,Bool.false_eq_true,Nat.testBit_xor,Nat.testBit_and,
      q5 _ hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide
lemma zh {k t S} (h : qy k t S) (i : Nat) (hi : i<252) :
    ∃ a ∈ S,(r9 (decide (0<t)) a).testBit i=true:= by
  induction h using qy.byInd with
  | stop =>
    refine ⟨qc,by simp,?_⟩
    simp [r9,qc,Nat.testBit_and,q5 _ hi,qg,hi]
  | unary _ _ _ ih =>
    obtain ⟨x,hx,h⟩:=ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,q1i _ _ _ hi h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,yj _ _ _ hi h⟩
  | binary _ _ _ _ _ ih =>
    obtain ⟨x,hx,h⟩:=ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases q0u _ _ _ _ _ hi h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
lemma ss (d : Bool) (v : List q0) (i : Nat) :
    (q9 d v).testBit i=true ↔ ∃ a ∈ v,(r9 d a).testBit i=true:= by
  induction v with
  | nil=>simp [q9]
  | cons a v ih =>
    simp only [q9,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons]
    constructor
    · rintro (h | ⟨b,hb,h⟩)
      · exact ⟨a,Or.inl rfl,h⟩
      · exact ⟨b,Or.inr hb,h⟩
    · rintro ⟨b,rfl | hb,h⟩
      · exact Or.inl h
      · exact Or.inr ⟨b,hb,h⟩
lemma q09 {k t S} {v : List q0} (h : qy k t S) (he : v.toFinset=S) :
    q9 (decide (0<t)) v=rx:= by
  apply Nat.eq_of_testBit_eq;intro i
  rw [qg]
  by_cases hi : i<252
  · obtain ⟨a,hm,ha⟩:=zh h i hi
    have hmem : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ hm)
    simp only [hi,decide_true]
    exact (ss _ _ _).2 ⟨a,hmem,ha⟩
  · simp only [hi,decide_false]
    rw [Bool.eq_false_iff];intro ht
    obtain ⟨a,ha,hbit⟩:=(ss _ _ _).1 ht
    have hv : qb a:=(qv h a (he ▸ List.mem_toFinset.mpr ha)).1
    have hf:=rq (decide (0<t)) hv i (by omega)
    rw [hf] at hbit;contradiction
lemma zm (d : Bool) (l r : List q0) :
    q9 d (l++r)=q9 d l|||q9 d r:= by
  induction l with
  | nil=>simp [q9]
  | cons a l ih=>simp [q9,ih,Nat.or_assoc]
def s8 (U : Finset q0) (del : List q0) : List q0 :=
  del.filter (fun a=>decide (a ∈ U))
lemma vz {v del : List q0} {U : Finset q0}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset=del.toFinset ∪ U) :
    (s8 U del++qw del v).Nodup/\(s8 U del++qw del v).toFinset=U:= by
  have memv (x : q0) : x ∈ v ↔ x ∈ del\/x ∈ U:= by
    rw [← List.mem_toFinset,he];simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq;subst b
    simp [s8] at ha;simp [qw] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,s8,qw,
      decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all
lemma u0 (del v : List q0) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del,x ∈ v) : v.Perm (del++qw del v):= by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e;subst b
    simp [qw] at hb;exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,qw,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all
lemma q2b (d : Bool) {v : List q0} {a : q0} (hv : v.Nodup) (hval : ∀ x ∈ v,qb x)
    (ha : a ∈ v) :
    v.length - 1=(qw [a] v).length ∧
      vr (qz d v) (r9 d a)=q9 d (qw [a] v):= by
  have p:=u0 [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l:=p.length_eq;simp at l;omega
  · rw [q0i d p hval]
    have hvd : ∀ x ∈ qw [a] v,qb x:=fun x hx =>
      hval x (p.mem_iff.mpr (List.mem_append_right _ hx))
    exact (q33 (ru d hvd) (rq d (hval a ha))).trans (zj _ _)
lemma q27 (d : Bool) {v : List q0} {a b : q0} (hv : v.Nodup)
    (hval : ∀ x ∈ v,qb x) (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length - 2=(qw [a,b] v).length ∧
      uc (qz d v) (r9 d a) (r9 d b)=q9 d (qw [a,b] v):= by
  have p:=u0 [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l:=p.length_eq;simp at l;omega
  · rw [q0i d p hval]
    have hvd : ∀ x ∈ qw [a,b] v,qb x:=fun x hx =>
      hval x (p.mem_iff.mpr (List.mem_append_right _ hx))
    exact (q32 (ru d hvd) (rq d (hval a ha))
      (rq d (hval b hb))).trans (zj _ _)
lemma q19 : rj.Nodup:= by decide +kernel
lemma rh : ∀ a ∈ rj,qb a:= by
  have hle : rj.all (fun a=>decide (a.1 ≤ rx/\a.2 ≤ rx))=true:= by decide +kernel
  intro a ha
  have h:=of_decide_eq_true (List.all_eq_true.mp hle a ha)
  exact ⟨uj h.1,uj h.2⟩
lemma q0d : rj.all (fun a=>q9 true (rj.erase a)!=rx)=true:= by
  decide +kernel
lemma q1l {k t S} (l : qy k t S) (hs : ∀ a ∈ S,a ∈ rj) : rj.toFinset=S:= by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr=>?_,hs a⟩
  by_contra hn
  have fail:=List.all_eq_true.mp q0d a hr
  have cov : q9 true (rj.erase a)=rx:= by
    apply Nat.eq_of_testBit_eq;intro i;rw [qg]
    by_cases hi : i<252
    · obtain ⟨b,hb,h⟩:=zh l i hi
      have ba : b ≠ a:=fun he=>hn (he ▸ hb)
      have hm:=(List.mem_erase_of_ne ba).mpr (hs _ hb)
      simp only [hi,decide_true]
      exact (ss true _ _).mpr ⟨b,hm,yj _ _ _ hi h⟩
    · simp only [hi,decide_false]
      rw [Bool.eq_false_iff];intro ht
      obtain ⟨b,hb,hbit⟩:=(ss true _ _).mp ht
      have hbv:=rh b (List.mem_of_mem_erase hb)
      have hf:=rq true hbv i (by omega)
      rw [hf] at hbit;contradiction
  simp [cov] at fail
def q0w : Nat:=0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0cb70ca41b4174c6b5c8dc87531b7a7a7a5074cd8a3e7ab966b5620c41cd99c659b5a7f5391beb8f399eb78a62dc8d4ea48db9593e7aec79a7c8b9b766e71b7a74f5ecdcc88f3e1b4141418a74b9505341cd0cec62667ab940f59beca7c6921beb87925db75062c89689e796cd9b5341b579a7dccdb7cddca741e29253e7a49bb5a77a7a7a50e20c8aec7a66b953f0cd410ccc928f531b39f5a7e359f5f4b78af0a49fdbdc9f668fec7a3ee41be766b7b9c8a77ae2393ea4e759eca74141418ae26650b5410ccd3ef0b97a66fa39873e1b92c6a7e39bc6f9b750f0e760f2c8600c87b54153e41ba40c
def q1k : Nat:=0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a51d000e00000eafaf3ca338a54e90779706a54e970505a39003060202a3970b06071d90030e0b653805a53c054e074e0b03af363c38e807a5a5a51d000e00000eafaf51e84ea538361a0306a538030505e83697066c6ce8030b06071d36970e0b654e05a551053807380b97af90514ea307a5a5a51d00af0000af0e0e774ee8a5a3363c0307a5a3030b0b4e36970744444e030507061d3697af0558e80ba5770ba306a305970e9077e83806a5a5a51d00af0000af0e0e1a38a3a5e890519707a5e8970b0b389003072c2c38970507061d9003af0558a30ba51a0be806e805030e361aa34e06a5a5a5
def v9 : Nat:=0x9a999e949592935d4f4e626355565354e3dedfdcdd5c5b79eb747877e9eae7e88972736a696f676e6b6d71706c68664029a6a5a43a39181110150e14121317160f0d0cb8b73e3f2728201f241c23212226251e1d1bcac9c83837989796f991908ffbfaa1a09ff7f8f5f69d9c9b6160525150db5a594d46454a494744484c4b434241e4e1e05f5ee2d9dad1d0d6d4d2cfd3d8d7ced5cd5857f0f18e8d7675f4e6e588876564eeefeced8c8b8af3f2867e7d83827f818584807c7b7accb5b63d1a19c7c6a3a2360504090806070b0a03020100cbb3b4abaab0aeacadb2b1a9a8afa73c3bc5bdbcc2c0bebfc4c3bbc1bab92f2e3332303135342d2c2b2a
def v8 : Nat:=0xa18c3d5f5e3c3bcce4cb8d8e9fa08a8b4063623f3e6061f3cac59d865c5b38373658572d302f2c323134332e2b352af4f2e3c8c9c6c7e2bbbebdbac0bfc3c2bcc4c1b99e8987889b9c7c7f7e7b828184837d85807a5d3a39595afbeeefb8e1b3b49a789875765655282752191af0f1faecedb7b5b6e0a9acabaeada8b1b0aab2afa779997796972954531e212023221d25241f261c1b5051eae9e5e6f8f7a6dfdea2a3dad9959473729164654f184d03060508070a0904010b0200ebe8e7f9f6f5a5a4dddcdbced2d1d4d3d7d6d0d8d5cfcd749392686b6a6e6d706f69716c67668f904e0f12111413161510170e0d0c43474649484b4a454c424441
def sw (key j : Nat) : Nat:=(key>>>(8*j))&&&255
def u7 (f : Nat->Nat) (x : Nat) : Nat->Nat->Nat
  | 0,acc=>acc
  | j+1,acc =>
    u7 f x j ((acc<<<1)|||(if x.testBit (f j) then 1 else 0))
def qu (f : Nat->Nat) (x : Nat) : Nat :=
  if x=0 then 0 else u7 f x 252 0
lemma u3 (f : Nat->Nat) (x : Nat) :
    ∀ (n acc k : Nat),(u7 f x n acc).testBit k =
      if k<n then x.testBit (f k) else acc.testBit (k - n)
  | 0,acc,k=>by simp [u7]
  | n+1,acc,k=>by
    rw [u7,u3]
    by_cases hk : k<n
    · simp [hk,show k<n+1 by omega]
    · by_cases heq : k=n
      · subst heq
        simp only [Nat.lt_irrefl,ite_false,Nat.lt_succ_self,ite_true,Nat.sub_self,
          Nat.testBit_or,Nat.testBit_shiftLeft,not_le.mpr Nat.zero_lt_one,
          decide_false,Bool.false_and,Bool.false_or]
        cases x.testBit (f k) <;> rfl
      · have h1 : ¬ k<n+1:= by omega
        have hsub : k - n=(k - (n+1))+1:= by omega
        simp only [hk,h1,ite_false,hsub,Nat.testBit_or,Nat.testBit_shiftLeft]
        have hbit : (if x.testBit (f n)=true then (1 : Nat) else 0).testBit (k - (n+1)+1)=false:= by
          cases x.testBit (f n) <;> simp [Nat.testBit_succ]
        rw [hbit,Bool.or_false]
        simp [show 1 ≤ k - (n+1)+1 by omega]
lemma ql (f : Nat->Nat) (x k : Nat) :
    (qu f x).testBit k=if k<252 then x.testBit (f k) else false:= by
  by_cases hx : x=0
  · subst hx;simp [qu]
  · rw [qu,ite_eq_right hx,u3];simp
lemma r7 (f : Nat->Nat) (x : Nat) : qr (qu f x):=fun j hj=>by
  rw [ql];simp [show ¬ j<252 by omega]
lemma sd (f : Nat->Nat) (a b : Nat) :
    qu f (a&&&b)=qu f a&&&qu f b:= by
  apply Nat.eq_of_testBit_eq;intro j
  simp only [Nat.testBit_and,ql];split_ifs <;> simp
lemma sm (f : Nat->Nat) (a b : Nat) :
    qu f (a|||b)=qu f a|||qu f b:= by
  apply Nat.eq_of_testBit_eq;intro j
  simp only [Nat.testBit_or,ql];split_ifs <;> simp
lemma ry (f : Nat->Nat) (hf : ∀ j<252,f j<252) (a : Nat) :
    qu f (rm a)=rm (qu f a):= by
  apply Nat.eq_of_testBit_eq;intro j
  rw [ql,uw (r7 f a),ql]
  by_cases hj : j<252
  · simp [hj,q5 a (hf j hj)]
  · simp [hj]
lemma rr (f : Nat->Nat) : qu f 0=0:= by
  apply Nat.eq_of_testBit_eq;intro j;rw [ql];split_ifs <;> simp
lemma sh (f : Nat->Nat) (hf : ∀ j<252,f j<252) : qu f rx=rx:= by
  apply Nat.eq_of_testBit_eq;intro j;rw [ql]
  by_cases hj : j<252
  · simp [hj,qg,hf j hj]
  · simp [hj,qg]
lemma ul (f : Nat->Nat) (hf : ∀ j<252,f j<252/\f (f j)=j)
    {a : Nat} (ha : qr a) : qu f (qu f a)=a:= by
  apply Nat.eq_of_testBit_eq;intro j
  rw [ql]
  by_cases hj : j<252
  · have hfj:=hf j hj
    rw [ite_eq_left hj,ql,ite_eq_left hfj.1,hfj.2]
  · rw [ite_eq_right hj];exact (ha j (by omega)).symm
lemma vx : ∀ j : Fin 252,sw v9 j.val<252/\sw v9 (sw v9 j.val)=j.val:= by
  decide +kernel
lemma vw : ∀ j : Fin 252,sw v8 j.val<252/\sw v8 (sw v8 j.val)=j.val:= by
  decide +kernel
lemma q15 : ∀ j : Fin 252,sw q0w j.val<252:= by decide +kernel
lemma q31 : ∀ j : Fin 252,sw q1k j.val<252:= by decide +kernel
def q3g (a : q0) : q0:=(qu (sw v9) a.1,qu (sw v9) a.2)
def q3f (a : q0) : q0:=(qu (sw v8) a.1,qu (sw v8) a.2)
def qj (isB : Bool) (a : q0) : q0:=if isB then q3f a else q3g a
def q1 : List Bool->q0->q0
  | [],a=>a
  | b :: t,a=>q1 t (qj b a)
def uu : Fin 8->List Bool :=
  ![[],[false],[false,true,false,true],[true,false,true],
    [true],[true,false],[false,true,false],[false,true]]
def r1 (g : Fin 8) (a : q0) : q0:=q1 (uu g) a
def zk (g : Fin 8) (a : q0) : q0:=q1 (uu g).reverse a
lemma uy (b : Bool) (a : q0) : qb (qj b a):= by
  cases b
  · exact ⟨r7 (sw v9) a.1,r7 (sw v9) a.2⟩
  · exact ⟨r7 (sw v8) a.1,r7 (sw v8) a.2⟩
lemma q0o (b : Bool) (a : q0) : qj b (qx a)=qx (qj b a):= by
  cases b
  · exact Prod.ext (ry (sw v9) (fun j hj=>(vx ⟨j,hj⟩).1) a.1)
      (ry (sw v9) (fun j hj=>(vx ⟨j,hj⟩).1) a.2)
  · exact Prod.ext (ry (sw v8) (fun j hj=>(vw ⟨j,hj⟩).1) a.1)
      (ry (sw v8) (fun j hj=>(vw ⟨j,hj⟩).1) a.2)
lemma q0p (b d : Bool) (x y : q0) :
    qj b (qn d x y)=qn d (qj b x) (qj b y):= by
  cases b <;> cases d
  · exact Prod.ext (sd (sw v9) x.1 y.1) (sd (sw v9) x.2 y.2)
  · exact Prod.ext (sm (sw v9) x.1 y.1) (sm (sw v9) x.2 y.2)
  · exact Prod.ext (sd (sw v8) x.1 y.1) (sd (sw v8) x.2 y.2)
  · exact Prod.ext (sm (sw v8) x.1 y.1) (sm (sw v8) x.2 y.2)
lemma zx (b : Bool) : qj b rv=rv:= by
  cases b
  · exact Prod.ext (rr (sw v9)) (rr (sw v9))
  · exact Prod.ext (rr (sw v8)) (rr (sw v8))
lemma q0n (b : Bool) : qj b v5=v5:= by
  cases b
  · have hA:=sh (sw v9) (fun j hj=>(vx ⟨j,hj⟩).1)
    simp only [qj,q3g,v5,Bool.false_eq_true,ite_false,hA]
  · have hB:=sh (sw v8) (fun j hj=>(vw ⟨j,hj⟩).1)
    simp only [qj,q3f,v5,ite_true,hB]
lemma z2 (b : Bool) : qj b qc=qc:= by
  cases b
  · have hA:=sh (sw v9) (fun j hj=>(vx ⟨j,hj⟩).1)
    simp only [qj,q3g,qc,Bool.false_eq_true,ite_false,hA,rr]
  · have hB:=sh (sw v8) (fun j hj=>(vw ⟨j,hj⟩).1)
    simp only [qj,q3f,qc,ite_true,hB,rr]
lemma vv (b : Bool) {a : q0} (ha : qb a) :
    qj b (qj b a)=a:= by
  cases b
  · exact Prod.ext (ul (sw v9) (fun j hj=>vx ⟨j,hj⟩) ha.1)
      (ul (sw v9) (fun j hj=>vx ⟨j,hj⟩) ha.2)
  · exact Prod.ext (ul (sw v8) (fun j hj=>vw ⟨j,hj⟩) ha.1)
      (ul (sw v8) (fun j hj=>vw ⟨j,hj⟩) ha.2)
lemma ze (w : List Bool) {a : q0} (ha : qb a) : qb (q1 w a):= by
  induction w generalizing a with
  | nil=>exact ha
  | cons b t ih=>exact ih (uy b a)
lemma us (w : List Bool) (a : q0) : q1 w (qx a)=qx (q1 w a):= by
  induction w generalizing a with
  | nil=>rfl
  | cons b t ih=>rw [q1,q0o,ih,q1]
lemma su (w : List Bool) (d : Bool) (x y : q0) :
    q1 w (qn d x y)=qn d (q1 w x) (q1 w y):= by
  induction w generalizing x y with
  | nil=>rfl
  | cons b t ih=>rw [q1,q0p,ih,q1,q1]
lemma xw (w : List Bool) : q1 w rv=rv:= by
  induction w with
  | nil=>rfl
  | cons b t ih=>rw [q1,zx,ih]
lemma q0l (w : List Bool) : q1 w v5=v5:= by
  induction w with
  | nil=>rfl
  | cons b t ih=>rw [q1,q0n,ih]
lemma vu (w : List Bool) : q1 w qc=qc:= by
  induction w with
  | nil=>rfl
  | cons b t ih=>rw [q1,z2,ih]
lemma z1 (w1 w2 : List Bool) (a : q0) :
    q1 (w1++w2) a=q1 w2 (q1 w1 a):= by
  induction w1 generalizing a with
  | nil=>rfl
  | cons b t ih=>exact ih (qj b a)
lemma ut (w : List Bool) {a : q0} (ha : qb a) :
    q1 w.reverse (q1 w a)=a:= by
  induction w generalizing a with
  | nil=>rfl
  | cons b t ih =>
    rw [List.reverse_cons,z1]
    simp only [q1]
    rw [ih (uy b a),vv b ha]
lemma sf (w : List Bool) {a b : q0} (ha : qb a) (hb : qb b)
    (he : q1 w a=q1 w b) : a=b:= by
  have h:=congrArg (q1 w.reverse) he
  rwa [ut w ha,ut w hb] at h
lemma ui (w : List Bool) {a : q0} (h : qd a) :
    qd (q1 w a):= by
  refine ⟨ze w h.1,?_,?_⟩
  · intro h0;exact h.2.1 (sf w h.1 vg (h0.trans (xw w).symm))
  · intro h1;exact h.2.2 (sf w h.1 q0r (h1.trans (q0l w).symm))
def si : Nat->q0
  | 0=>x3 | 1=>q1d | 2=>q1c | 3=>yv
  | 4=>q1b | 5=>yu | 6=>yt | 7=>q1a | _=>rv
lemma y4 (j : Nat) : qb (si j):= by
  match j with
  | 0=>exact rh x3 (by simp [rj])
  | 1=>exact rh q1d (by simp [rj])
  | 2=>exact rh q1c (by simp [rj])
  | 3=>exact rh yv (by simp [rj])
  | 4=>exact rh q1b (by simp [rj])
  | 5=>exact rh yu (by simp [rj])
  | 6=>exact rh yt (by simp [rj])
  | 7=>exact rh q1a (by simp [rj])
  | _+8=>exact vg
def u8 (isB : Bool) (j : Nat) : Nat :=
  ((if isB then 0x43076215 else 0x25613740)>>>(4*j))&&&7
def vo : List Bool->Nat->Nat
  | [],j=>j
  | b :: t,j=>vo t (u8 b j)
set_option maxRecDepth 10000 in
lemma x8 : ∀ (b : Bool) (j : Fin 8),
    qj b (si j.val)=si (u8 b j.val):= by decide +kernel
lemma q06 (b : Bool) (j : Nat) : u8 b j<8:= by
  have h : u8 b j ≤ 7:=Nat.and_le_right
  omega
lemma s3 (w : List Bool) : ∀ (j : Nat),j<8 →
    q1 w (si j)=si (vo w j):= by
  induction w with
  | nil=>intro j _;rfl
  | cons b t ih =>
    intro j hj
    rw [q1,x8 b ⟨j,hj⟩,vo]
    exact ih (u8 b j) (q06 b j)
def qf : List q0:=[x3,yv,yu,yt]
def qa (a : q0) : Bool :=
  rg a x3||rg a yv||rg a yu||rg a yt
lemma ri (a : q0) : qa a=true ↔ a ∈ qf:= by
  simp only [qa,qf,Bool.or_eq_true,rf,List.mem_cons,List.not_mem_nil,or_false]
  tauto
def s5 : Fin 4->q0:=![x3,yv,yu,yt]
def sp : Fin 4->Fin 8:=![0,2,4,6]
lemma yr : ∀ a ∈ qf,qb a:=fun a ha =>
  rh a (by simp only [qf,rj,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢;tauto)
lemma sy (b : Bool) (l : List Nat) (hl : ∀ j ∈ l,j<8)
    (hp : (l.map (u8 b)).Perm l) :
    ((l.map si).map (qj b)).Perm (l.map si):= by
  have heq : (l.map si).map (qj b)=(l.map (u8 b)).map si:= by
    rw [List.map_map,List.map_map]
    exact List.map_congr_left fun j hj=>x8 b ⟨j,hl j hj⟩
  rw [heq];exact hp.map si
lemma yb (b : Bool) : (qf.map (qj b)).Perm qf:= by
  change (([0,3,5,6].map si).map (qj b)).Perm ([0,3,5,6].map si)
  exact sy b [0,3,5,6] (by decide) (by cases b <;> decide)
lemma x0 (b : Bool) {a : q0} (ha : qb a) :
    qj b a ∈ qf ↔ a ∈ qf:= by
  have hp:=yb b
  rw [← hp.mem_iff]
  constructor
  · intro hm;obtain ⟨x,hx,he⟩:=List.mem_map.mp hm
    have hinv : x=a:= by
      have h:=congrArg (qj b) he
      rwa [vv b (yr x hx),vv b ha] at h
    exact hinv ▸ hx
  · exact List.mem_map_of_mem
lemma s1 (w : List Bool) {a : q0} (ha : qb a) :
    q1 w a ∈ qf ↔ a ∈ qf:= by
  induction w generalizing a with
  | nil=>rfl
  | cons b t ih=>rw [q1,ih (uy b a),x0 b ha]
lemma q0m (b : Bool) : (rj.map (qj b)).Perm rj:= by
  change (([0,1,2,3,4,5,6,7].map si).map (qj b)).Perm ([0,1,2,3,4,5,6,7].map si)
  exact sy b [0,1,2,3,4,5,6,7] (by decide) (by cases b <;> decide)
lemma y2 (w : List Bool) : (rj.map (q1 w)).Perm rj:= by
  induction w with
  | nil=>simp [q1]
  | cons b t ih =>
    have hs:=q0m b
    have hm : rj.map (q1 (b :: t))=(rj.map (qj b)).map (q1 t):= by
      rw [List.map_map];rfl
    rw [hm];exact (hs.map (q1 t)).trans ih
def xt (a : q0) : q0:=(qu (sw q0w) a.1,qu (sw q1k) a.2)
def q3 (i : Fin 4) (a : q0) : q0:=xt (r1 (sp i) a)
lemma re (i : Fin 4) (a : q0) : qb (q3 i a) :=
  ⟨r7 (sw q0w) (r1 (sp i) a).1,
   r7 (sw q1k) (r1 (sp i) a).2⟩
lemma uo (i : Fin 4) (a : q0) : q3 i (qx a)=qx (q3 i a):= by
  rw [q3,q3,r1,r1,us]
  exact Prod.ext (ry (sw q0w) (fun j hj=>q15 ⟨j,hj⟩) _)
    (ry (sw q1k) (fun j hj=>q31 ⟨j,hj⟩) _)
lemma vn (i : Fin 4) (d : Bool) (a b : q0) :
    q3 i (qn d a b)=qn d (q3 i a) (q3 i b):= by
  rw [q3,q3,q3,r1,r1,r1,su]
  cases d
  · exact Prod.ext (sd (sw q0w) _ _) (sd (sw q1k) _ _)
  · exact Prod.ext (sm (sw q0w) _ _) (sm (sw q1k) _ _)
lemma zp : xt qc=qc:= by
  have hP:=sh (sw q0w) (fun j hj=>q15 ⟨j,hj⟩)
  simp only [xt,qc,hP,rr]
lemma vm (i : Fin 4) : q3 i qc=qc:= by
  rw [q3,r1,vu,zp]
set_option maxRecDepth 10000 in
lemma yo : xt x3=rv:= by decide +kernel
lemma zd (i : Fin 4) : r1 (sp i) (s5 i)=x3:= by
  fin_cases i
  · exact s3 _ 0 (by omega)
  · exact s3 _ 3 (by omega)
  · exact s3 _ 5 (by omega)
  · exact s3 _ 6 (by omega)
lemma r8 (i : Fin 4) : q3 i (s5 i)=rv:= by
  rw [q3,zd i,yo]
def r4 (a : q0) : Nat :=
  ((a.1&&&Theta.lo 232)<<<232)|||(a.2&&&Theta.lo 232)
lemma uv (a : q0) (j : Nat) :
    (r4 a).testBit j =
      if j<232 then a.2.testBit j else if j<464 then a.1.testBit (j - 232) else false:= by
  simp only [r4,Theta.lo,Nat.testBit_or,Nat.testBit_and,
    Nat.testBit_two_pow_sub_one,Nat.testBit_shiftLeft]
  by_cases hj : j<232
  · simp [hj,show ¬ 232 ≤ j by omega]
  · by_cases hk : j<464
    · simp [hj,hk,show 232 ≤ j by omega,show j - 232<232 by omega]
    · simp [hj,hk,show 232 ≤ j by omega,show ¬ j - 232<232 by omega]
lemma xy : r4 qc=Theta.goal 232:= by decide +kernel
lemma z4 (a : q0) :
    r4 (qx a)=r4 a^^^Theta.mask 232:= by
  have hmask (j : Nat) : (Theta.mask 232).testBit j=decide (j<464):= by
    simp only [Theta.mask,Theta.lo,Nat.testBit_two_pow_sub_one]
  apply Nat.eq_of_testBit_eq;intro j
  rw [Nat.testBit_xor,hmask,uv,uv]
  by_cases hl : j<232
  · simp [hl,qx,q5 _ (show j<252 by omega),show j<464 by omega]
  · by_cases hh : j<464
    · simp [hl,hh,qx,q5 _ (show j - 232<252 by omega)]
    · simp [hl,hh]
lemma x2 (d : Bool) (a b : q0) :
    r4 (qn d a b)=if d then r4 a|||r4 b else r4 a&&&r4 b:= by
  apply Nat.eq_of_testBit_eq;intro j
  cases d <;> simp only [qn,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_or,
    Nat.testBit_and,uv] <;> split_ifs <;> rfl
lemma q1m {k t S} (h : qy k t S) (v : List q0) (hv : v.Nodup)
    (he : v.toFinset=S) :
    Theta.Run qx (qn false) (qn true) qc k v:= by
  induction h using qy.byInd generalizing v with
  | stop =>
    have hp : ([qc] : List q0).Perm v :=
      List.perm_of_nodup_nodup_toFinset_eq (by simp) hv (by simp [he])
    exact Theta.Run.perm hp Theta.Run.done
  | @unary k t U a _ hf _ ih =>
    let rest:=qw [a] v
    have ham : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    obtain ⟨hn,eq⟩:=vz (del:=[a]) hv (by simp) (by simpa using he)
    let save:=decide (a ∈ U)
    have hkeep : Theta.kept save a rest=s8 U [a]++rest:= by
      by_cases hm : a ∈ U <;> simp [save,Theta.kept,s8,hm]
    rw [← hkeep] at hn eq
    have hs : (qx a :: Theta.kept save a rest).toFinset=insert (qx a) U:= by
      rw [List.toFinset_cons,eq]
    have hnd : (qx a :: Theta.kept save a rest).Nodup:= by
      refine List.nodup_cons.mpr ⟨fun hz=>hf (Finset.mem_insert_of_mem ?_),hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p:=u0 [a] v hv (by simp) (by simpa using ham)
    exact Theta.Run.perm p.symm (Theta.Run.one true save (ih _ hnd hs))
  | @binary k t U a b d _ _ hab hf _ ih =>
    let rest:=qw [a,b] v
    have ah : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bh : b ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    obtain ⟨hn,eq⟩:=vz (del:=[a,b]) hv (by simp [hab]) (by simpa using he)
    let sa:=decide (a ∈ U);let sb:=decide (b ∈ U)
    have hkeep : Theta.kept sa a (Theta.kept sb b rest)=s8 U [a,b]++rest:= by
      by_cases ham : a ∈ U <;> by_cases hbm : b ∈ U <;> simp [sa,sb,Theta.kept,s8,ham,hbm]
    rw [← hkeep] at hn eq
    have hs : (qn d a b :: Theta.kept sa a (Theta.kept sb b rest)).toFinset=insert (qn d a b) U:= by
      rw [List.toFinset_cons,eq]
    have hnd : (qn d a b :: Theta.kept sa a (Theta.kept sb b rest)).Nodup:= by
      refine List.nodup_cons.mpr ⟨fun hz=>hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)),hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p:=u0 [a,b] v hv (by simp [hab]) (by simpa using And.intro ah bh)
    have hdone:=ih _ hnd hs
    cases d
    · exact Theta.Run.perm p.symm (Theta.Run.two true sa sb hdone)
    · exact Theta.Run.perm p.symm (Theta.Run.two false sa sb hdone)
def vi : List q0:=[q1c,q1a,yv,q1d,yu,yt,q1b]
def rc : List q0:=vi.map xt
lemma yg : vi.toFinset=rj.toFinset.erase x3:= by decide +kernel
lemma x4 (i : Fin 4) : s5 i ∈ rj.toFinset:= by
  fin_cases i <;> decide +kernel
set_option maxRecDepth 10000 in
lemma uk : rc.map r4=Theta.xs517:= by decide +kernel
lemma xx : Theta.xs517.Nodup:= by decide +kernel
lemma y8 : rc.Nodup:= by
  have h:=xx;rw [← uk] at h;exact List.Nodup.of_map _ h
lemma q04 (i : Fin 4) :
    rj.toFinset.image (q3 i)=insert rv rc.toFinset:= by
  have hact : rj.toFinset.image (r1 (sp i))=rj.toFinset:= by
    ext x;simp only [Finset.mem_image,List.mem_toFinset]
    have hp:=y2 (uu (sp i))
    rw [← hp.mem_iff,List.mem_map];rfl
  have hcomp : rj.toFinset.image (q3 i)=rj.toFinset.image xt:= by
    calc rj.toFinset.image (q3 i)
        = (rj.toFinset.image (r1 (sp i))).image xt:= by
          rw [Finset.image_image];rfl
      _=rj.toFinset.image xt:= by rw [hact]
  have hm : rc.toFinset=vi.toFinset.image xt:= by
    ext a;simp [rc,Finset.mem_image,List.mem_map]
  have h0 : x3 ∈ rj.toFinset:=x4 0
  rw [hcomp,hm,yg,← yo,← Finset.image_insert,Finset.insert_erase h0]
def qm (w : List q0) (v : q0) : Prop:=v ∈ w\/¬ qd v
lemma s2 {w : List q0} {a : q0} (haV : qb a) (h : qm w a) :
    a=rv\/a=v5\/(a ∈ w/\qd a):= by
  by_cases hz : a=rv
  · exact Or.inl hz
  by_cases ho : a=v5
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x=>x ⟨haV,hz,ho⟩),haV,hz,ho⟩)
def yc (w : List q0) (z : q0) : Prop :=
  (∃ a ∈ w,qd a/\z=qx a) ∨
  (∃ d a b,a ∈ w/\b ∈ w/\qd a/\qd b/\a ≠ b/\z=qn d a b)
lemma q35 {w a b} (d : Bool) (haV : qb a) (hbV : qb b)
    (ha : qm w a) (hb : qm w b) :
    qm w (qn d a b)\/yc w (qn d a b):= by
  have rz : qm w rv:=Or.inr (fun h=>h.2.1 rfl)
  have ro : qm w v5:=Or.inr (fun h=>h.2.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩:=so haV
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩:=so hbV
  rcases s2 haV ha with rfl | rfl | ⟨ham,hap⟩
  · rw [s0];cases d <;> simp_all
  · rw [s0];cases d <;> simp_all
  rcases s2 hbV hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b;cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)
lemma q30 (w : List q0) (a : q0) (haV : qb a) (ha : a ∈ w) :
    qm w (qx a)\/yc w (qx a):= by
  rcases s2 haV (Or.inl ha : qm w a) with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr (fun hh=>hh.2.2 v6.1))
  · exact Or.inl (Or.inr (fun hh=>hh.2.1 v6.2))
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
lemma q1j {w : List q0} {z : q0} {k t S} (h : qy k t S)
    (hz : qm w z\/yc w z) (sub : ∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1/\qy k' t' S'/\∀ a ∈ S',a ∈ w:= by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w\/a=z:= by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp:=qv h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U:=S.erase (qx a)
        have ht : qy k t (insert (qx a) U):= by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:= by
          intro v hv;obtain ⟨hne,hmv⟩:=Finset.mem_erase.mp hv;simpa [hne] using sub v hmv
        have hf : qx a ∉ insert a U:= by
          intro hh;rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,qy.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U:=S.erase (qn d a b)
        have ht : qy k t (insert (qn d a b) U):= by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U,v ∈ w:= by
          intro v hv;obtain ⟨hne,hmv⟩:=Finset.mem_erase.mp hv;simpa [hne] using sub v hmv
        have hf : qn d a b ∉ insert a (insert b U):= by
          intro hh;rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,qy.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha;have hn : a ≠ z:=fun hh=>hm (hh ▸ ha);simpa [hn] using sub a ha
def qp (i : Fin 4) (k : Nat) (S : Finset q0) : Prop :=
  ∃ m ≤ k,∃ t T,qy m t T/\T ⊆ S.image (q3 i)
lemma v2 (i : Fin 4) : ¬ qp i 10 rj.toFinset:= by
  rintro ⟨m,hm,t,T,h,hs⟩
  rw [q04] at hs
  have ht : ∀ a ∈ T,a ∈ rc:= by
    intro a ha
    rcases Finset.mem_insert.mp (hs ha) with eq | hmem
    · exact False.elim ((qv h _ ha).2.1 eq)
    · exact List.mem_toFinset.mp hmem
  let v:=rc.filter (fun a=>decide (a ∈ T))
  have he : v.toFinset=T:= by
    ext a;simp only [v,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun ha=>⟨ht _ ha,ha⟩⟩
  have hh:=q1m h v (y8.filter _) he
  have hr:=Theta.Run.map (inv':=(·^^^Theta.mask 232))
    (meet':=(·&&&·)) (join':=(·|||·)) r4 z4
    (fun a b=>x2 false a b) (fun a b=>x2 true a b) hh
  rw [xy] at hr
  apply Theta.noSub hm _ hr
  have sub:=List.Sublist.map r4
    (List.filter_sublist (l:=rc) (p:=fun a=>decide (a ∈ T)))
  rwa [uk] at sub
lemma za {i : Fin 4} {k k' : Nat} {S : Finset q0}
    (h : qp i k S) (hk : k ≤ k') : qp i k' S:= by
  obtain ⟨m,hm,t,T,hl,hs⟩:=h;exact ⟨m,hm.trans hk,t,T,hl,hs⟩
lemma x5 {i : Fin 4} {q : Nat} {S S' : Finset q0} {g : q0}
    (hs : S' ⊆ insert g S)
    (hr : qm (S.image (q3 i)).toList (q3 i g) ∨
      yc (S.image (q3 i)).toList (q3 i g))
    (h : qp i q S') : qp i (q+1) S:= by
  obtain ⟨m,hm,t,T,hl,ht⟩:=h
  have sub : ∀ a ∈ T,a ∈ (S.image (q3 i)).toList++[q3 i g]:= by
    intro a ha;obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp (ht ha)
    rcases Finset.mem_insert.mp (hs hb) with rfl | hb
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hb))
  obtain ⟨m',t',T',hm',h',hT'⟩:=q1j hl hr sub
  exact ⟨m',by omega,t',T',h',fun a ha=>Finset.mem_toList.mp (hT' _ ha)⟩
lemma x6 {i : Fin 4} {q : Nat} {S S' : Finset q0} {g : q0}
    (hs : S' ⊆ insert g S)
    (hr : qm (S.image (q3 i)).toList (q3 i g))
    (h : qp i q S') : qp i q S:= by
  obtain ⟨m,hm,t,T,hl,ht⟩:=h
  refine ⟨m,hm,t,T,hl,?_⟩
  intro a ha;obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp (ht ha)
  rcases Finset.mem_insert.mp (hs hb) with rfl | hb
  · exact Finset.mem_toList.mp (hr.resolve_right (fun hp=>hp (qv hl _ ha)))
  · exact Finset.mem_image_of_mem _ hb
lemma va {i : Fin 4} {q : Nat} {a : q0} {U : Finset q0}
    (h : qp i q (insert (qx a) U)) : qp i (q+1) (insert a U):= by
  apply x5 (g:=qx a) (by simp [Finset.insert_subset_iff];exact fun _ h=>by simp [h]) _ h
  rw [uo]
  exact q30 _ _ (re i a) (by simp)
lemma un {i : Fin 4} {q : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (h : qp i q (insert (qn d a b) U)) : qp i (q+1) (insert a (insert b U)):= by
  apply x5 (g:=qn d a b) (by simp [Finset.insert_subset_iff];exact fun _ h=>by simp [h]) _ h
  rw [vn]
  exact q35 _ (re i a) (re i b) (Or.inl (by simp)) (Or.inl (by simp))
lemma xj {i : Fin 4} {q : Nat} {a : q0} {U : Finset q0}
    (ha : ¬ qd (q3 i a)) (h : qp i q (insert (qx a) U)) :
    qp i q (insert a U):= by
  apply x6 (g:=qx a) (by simp [Finset.insert_subset_iff];exact fun _ h=>by simp [h]) _ h
  rcases s2 (re i a) (Or.inr ha : qm [] (q3 i a)) with hz | ho | hm
  · exact Or.inr (fun hp=>hp.2.2 (by rw [uo,hz,v6.1]))
  · exact Or.inr (fun hp=>hp.2.1 (by rw [uo,ho,v6.2]))
  · simp at hm
lemma rn {i : Fin 4} {q : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (ha : ¬ qd (q3 i a)) (h : qp i q (insert (qn d a b) U)) :
    qp i q (insert a (insert b U)):= by
  apply x6 (g:=qn d a b) (by simp [Finset.insert_subset_iff];exact fun _ h=>by simp [h]) _ h
  rw [vn,s0]
  have hbv:=re i b
  rcases s2 (re i a) (Or.inr ha : qm [] (q3 i a)) with hz | ho | hm
  · rw [hz]
    cases d
    · exact Or.inr (fun hp=>hp.2.1 (so hbv).2.2.1)
    · rw [(so hbv).2.1];exact Or.inl (by simp)
  · rw [ho]
    cases d
    · rw [(so hbv).1];exact Or.inl (by simp)
    · exact Or.inr (fun hp=>hp.2.2 (so hbv).2.2.2.1)
  · simp at hm
lemma uq {i : Fin 4} {q : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (hb : ¬ qd (q3 i b)) (h : qp i q (insert (qn d a b) U)) :
    qp i q (insert a (insert b U)):= by
  rw [s0] at h;rw [Finset.insert_comm];exact rn hb h
lemma ud {k t : Nat} {S : Finset q0} (h : qy k t S) (i : Fin 4) :
    qp i k S:= by
  induction h using qy.byInd with
  | stop=>refine ⟨0,Nat.le_refl _,0,{qc},qy.stop,?_⟩;simp [vm]
  | unary _ _ _ ih=>exact va ih
  | binary _ _ _ _ _ ih=>exact un ih
lemma ue {k t : Nat} {S : Finset q0} (h : qy k t S)
    (i : Fin 4) (a : q0) (ha : a ∈ S) (hc : ¬ qd (q3 i a)) :
    ∃ q<k,qp i q S:= by
  induction h using qy.byInd with
  | stop =>
    have ht : a=qc:=Finset.mem_singleton.mp ha
    exact (hc (by rw [ht,vm];exact vq)).elim
  | @unary k t U b _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨k,by omega,xj hc (ud tail i)⟩
    · obtain ⟨q,hq,h⟩:=ih (Finset.mem_insert_of_mem ha);exact ⟨q+1,by omega,va h⟩
  | @binary k t U b c d _ _ _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | hU
    · exact ⟨k,by omega,rn hc (ud tail i)⟩
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨k,by omega,uq hc (ud tail i)⟩
      · obtain ⟨q,hq,h⟩:=ih (Finset.mem_insert_of_mem hU);exact ⟨q+1,by omega,un h⟩
def r3 (k : Nat) (S : Finset q0) : Prop :=
  ∀ i q,q+(if s5 i ∈ S then 1 else 0)<k->¬ qp i q S
lemma xf {k : Nat} (hk : k ≤ 12) : r3 k rj.toFinset:= by
  intro i q hq h;rw [ite_eq_left (x4 i)] at hq
  exact v2 i (za h (by omega))
lemma xu (a : q0) : a ∈ qf ↔ ∃ i,s5 i=a:= by
  rw [← List.mem_ofFn];rfl
lemma q0j {k : Nat} {a : q0} {U : Finset q0}
    (h : r3 (k+1) (insert a U)) : r3 k (insert (qx a) U):= by
  intro i q hq hf
  by_cases hp : s5 i ∈ insert a U
  · by_cases ht : s5 i ∈ insert (qx a) U
    · rw [ite_eq_left ht] at hq;exact h i (q+1) (by simp [hp];omega) (va hf)
    · rw [ite_eq_right ht] at hq
      have he : s5 i=a :=
        (Finset.mem_insert.mp hp).resolve_right (fun hm=>ht (Finset.mem_insert_of_mem hm))
      have hz : ¬ qd (q3 i a):= by rw [← he,r8];exact fun hz=>hz.2.1 rfl
      exact h i q (by simp [hp];omega) (xj hz hf)
  · exact h i (q+1) (by simp [hp];split at hq <;> omega) (va hf)
lemma zv {k : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (h : r3 (k+1) (insert a (insert b U))) : r3 k (insert (qn d a b) U):= by
  intro i q hq hf
  by_cases hp : s5 i ∈ insert a (insert b U)
  · by_cases ht : s5 i ∈ insert (qn d a b) U
    · rw [ite_eq_left ht] at hq;exact h i (q+1) (by simp [hp];omega) (un hf)
    · rw [ite_eq_right ht] at hq
      rcases Finset.mem_insert.mp hp with ha | hb
      · have hz : ¬ qd (q3 i a):= by rw [← ha,r8];exact fun hz=>hz.2.1 rfl
        exact h i q (by simp [hp];omega) (rn hz hf)
      · rcases Finset.mem_insert.mp hb with hb | hU
        · have hz : ¬ qd (q3 i b):= by rw [← hb,r8];exact fun hz=>hz.2.1 rfl
          exact h i q (by simp [hp];omega) (uq hz hf)
        · exact (ht (Finset.mem_insert_of_mem hU)).elim
  · exact h i (q+1) (by simp [hp];split at hq <;> omega) (un hf)
lemma xz {k t : Nat} {a : q0} {U : Finset q0}
    (h : r3 (k+1) (insert a U)) (tail : qy k t (insert (qx a) U)) :
    a ∉ qf:= by
  intro hm;obtain ⟨i,rfl⟩:=(xu _).mp hm
  have hz : ¬ qd (q3 i (s5 i)):= by rw [r8];exact fun hz=>hz.2.1 rfl
  have ho : ¬ qd (q3 i (qx (s5 i))):= by
    rw [uo,r8,v6.1];exact fun hp=>hp.2.2 rfl
  obtain ⟨q,hq,hf⟩:=ue tail i (qx (s5 i)) (Finset.mem_insert_self _ _) ho
  exact h i q (by simp;omega) (xj hz hf)
lemma xp {k t : Nat} {a b : q0} {d : Bool} {U : Finset q0}
    (h : r3 (k+1) (insert a (insert b U))) (tail : qy k t (insert (qn d a b) U)) :
    (a ∈ qf->d=true/\a ∉ U)/\(b ∈ qf->d=true/\b ∉ U):= by
  have leftSide {a b : q0} (h : r3 (k+1) (insert a (insert b U)))
      (tail : qy k t (insert (qn d a b) U)) (hm : a ∈ qf) : d=true/\a ∉ U:= by
    obtain ⟨i,rfl⟩:=(xu _).mp hm
    have hz : ¬ qd (q3 i (s5 i)):= by rw [r8];exact fun hz=>hz.2.1 rfl
    constructor
    · cases d
      · exfalso
        have ho : ¬ qd (q3 i (qn false (s5 i) b)):= by
          rw [vn,r8,s0,(so (re i b)).2.2.1]
          exact fun hp=>hp.2.1 rfl
        obtain ⟨q,hq,hf⟩:=ue tail i _ (Finset.mem_insert_self _ _) ho
        exact h i q (by simp;omega) (rn hz hf)
      · rfl
    · intro hU
      obtain ⟨q,hq,hf⟩:=ue tail i _ (Finset.mem_insert_of_mem hU) hz
      exact h i q (by simp;omega) (rn hz hf)
  refine ⟨leftSide h tail,?_⟩
  apply leftSide (a:=b) (b:=a)
  · rwa [Finset.insert_comm]
  · rwa [s0]
def q2  (k t : Nat) (S : Finset q0) : Prop :=
  ∀ (P : Nat → Nat → Finset q0 → Prop),(P 0 0 {qc}) →
    (∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hf : qx a ∉ insert a U) (hr : a ∉ qf) (ih : P k t (insert (qx a) U)),P (k+1) (t+1) (insert a U)) →
    (∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hf : qn d a b ∉ insert a (insert b U))
      (hra : a ∈ qf→d=true/\a ∉ U)
      (hrb : b ∈ qf→d=true/\b ∉ U) (ih : P k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U))) → P k t S
theorem q2.stop   : q2 0 0 {qc}:=by
  intro P stop unary binary
  exact @stop
theorem q2.unary  {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hf : qx a ∉ insert a U) (hr : a ∉ qf) (tail : q2 k t (insert (qx a) U)) : q2 (k+1) (t+1) (insert a U):=by
  intro P stop unary binary
  exact @unary k t U a ha hf hr (tail P stop unary binary)
theorem q2.binary  {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hf : qn d a b ∉ insert a (insert b U))
      (hra : a ∈ qf→d=true/\a ∉ U)
      (hrb : b ∈ qf→d=true/\b ∉ U) (tail : q2 k t (insert (qn d a b) U)) : q2 (k+1) t (insert a (insert b U)):=by
  intro P stop unary binary
  exact @binary k t U a b d ha hb hab hf hra hrb (tail P stop unary binary)
theorem q2.elimInd  {P : Nat → Nat → Finset q0 → Prop}
    (stop : P 0 0 {qc})
    (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hf : qx a ∉ insert a U) (hr : a ∉ qf) (tail : q2 k t (insert (qx a) U)) (ih : P k t (insert (qx a) U)),P (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hf : qn d a b ∉ insert a (insert b U))
      (hra : a ∈ qf→d=true/\a ∉ U)
      (hrb : b ∈ qf→d=true/\b ∉ U) (tail : q2 k t (insert (qn d a b) U)) (ih : P k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U))) {k t : Nat} {S : Finset q0} (h : q2 k t S) : P k t S:=by
  apply And.right (a:=q2 k t S)
  apply h (fun k t S=>q2 k t S ∧ P k t S)
  · exact ⟨@q2.stop  ,@stop  ⟩
  · intro k t U a ha hf hr prev
    exact ⟨@q2.unary k t U a ha hf hr prev.1,@unary k t U a ha hf hr prev.1 prev.2⟩
  · intro k t U a b d ha hb hab hf hra hrb prev
    exact ⟨@q2.binary k t U a b d ha hb hab hf hra hrb prev.1,@binary k t U a b d ha hb hab hf hra hrb prev.1 prev.2⟩
theorem q2.elimCases  {P : Nat → Nat → Finset q0 → Prop}
    (stop : P 0 0 {qc})
    (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hf : qx a ∉ insert a U) (hr : a ∉ qf) (tail : q2 k t (insert (qx a) U)),P (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hf : qn d a b ∉ insert a (insert b U))
      (hra : a ∈ qf→d=true/\a ∉ U)
      (hrb : b ∈ qf→d=true/\b ∉ U) (tail : q2 k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U))) {k t : Nat} {S : Finset q0} (h : q2 k t S) : P k t S:=by
  apply q2.elimInd (P:=P) (h:=h)
  · exact @stop
  · intro k t U a ha hf hr prev ih
    exact @unary k t U a ha hf hr prev
  · intro k t U a b d ha hb hab hf hra hrb prev ih
    exact @binary k t U a b d ha hb hab hf hra hrb prev
theorem q2.byInd  {P : ∀ (k t : Nat) (S : Finset q0),q2 k t S → Prop}
  (stop : P 0 0 {qc} (@q2.stop ))
  (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hf : qx a ∉ insert a U) (hr : a ∉ qf) (tail : q2 k t (insert (qx a) U)) (ih : P k t (insert (qx a) U) tail),P (k+1) (t+1) (insert a U) (@q2.unary k t U a ha hf hr tail))
  (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hf : qn d a b ∉ insert a (insert b U))
      (hra : a ∈ qf→d=true/\a ∉ U)
      (hrb : b ∈ qf→d=true/\b ∉ U) (tail : q2 k t (insert (qn d a b) U)) (ih : P k t (insert (qn d a b) U) tail),P (k+1) t (insert a (insert b U)) (@q2.binary k t U a b d ha hb hab hf hra hrb tail)) {k t : Nat} {S : Finset q0} (h : q2 k t S) : P k t S h:=by
  have aux : ∀ hx : q2 k t S,P k t S hx:=by
    apply q2.elimInd (P:=fun k t S=>∀ hx : q2 k t S,P k t S hx) (h:=h)
    · intro  hx
      exact @stop
    · intro k t U a ha hf hr prev ih hx
      exact @unary k t U a ha hf hr prev (ih prev)
    · intro k t U a b d ha hb hab hf hra hrb prev ih hx
      exact @binary k t U a b d ha hb hab hf hra hrb prev (ih prev)
  exact aux h
theorem q2.byCases  {P : ∀ (k t : Nat) (S : Finset q0),q2 k t S → Prop}
  (stop : P 0 0 {qc} (@q2.stop ))
  (unary : ∀ {k t : Nat} {U : Finset q0} {a : q0} (ha : qd a)
      (hf : qx a ∉ insert a U) (hr : a ∉ qf) (tail : q2 k t (insert (qx a) U)),P (k+1) (t+1) (insert a U) (@q2.unary k t U a ha hf hr tail))
  (binary : ∀ {k t : Nat} {U : Finset q0} {a b : q0} {d : Bool}
      (ha : qd a) (hb : qd b) (hab : a ≠ b)
      (hf : qn d a b ∉ insert a (insert b U))
      (hra : a ∈ qf→d=true/\a ∉ U)
      (hrb : b ∈ qf→d=true/\b ∉ U) (tail : q2 k t (insert (qn d a b) U)),P (k+1) t (insert a (insert b U)) (@q2.binary k t U a b d ha hb hab hf hra hrb tail)) {k t : Nat} {S : Finset q0} (h : q2 k t S) : P k t S h:=by
  have aux : ∀ hx : q2 k t S,P k t S hx:=by
    apply q2.elimCases (P:=fun k t S=>∀ hx : q2 k t S,P k t S hx) (h:=h)
    · intro  hx
      exact @stop
    · intro k t U a ha hf hr prev hx
      exact @unary k t U a ha hf hr prev
    · intro k t U a b d ha hb hab hf hra hrb prev hx
      exact @binary k t U a b d ha hb hab hf hra hrb prev
  exact aux h
lemma q2.nlive {k t S} (h : q2 k t S) : qy k t S:= by
  induction h using q2.byInd with
  | stop=>exact qy.stop
  | unary ha hf _ _ ih=>exact qy.unary ha hf ih
  | binary ha hb hab hf _ _ _ ih=>exact qy.binary ha hb hab hf ih
lemma yl {k t S} (h : qy k t S) (hb : r3 k S) : q2 k t S:= by
  induction h using qy.byInd with
  | stop=>exact q2.stop
  | unary ha hf tail ih =>
    exact q2.unary ha hf (xz hb tail) (ih (q0j hb))
  | binary ha hg hab hf tail ih =>
    obtain ⟨h1,h2⟩:=xp hb tail
    exact q2.binary ha hg hab hf h1 h2 (ih (zv hb))
lemma xe (w : List Bool) {k t : Nat} {S : Finset q0}
    (h : q2 k t S) : q2 k t (S.image (q1 w)):= by
  induction h using q2.byInd with
  | stop=>simpa [vu] using q2.stop
  | @unary k t U a ha hf hr tail ih =>
    have hU : ∀ x ∈ U,qb x:=fun x hx =>
      (qv tail.nlive x (Finset.mem_insert_of_mem hx)).1
    simp only [Finset.image_insert,us] at ih ⊢
    have hne : qx (q1 w a) ∉ insert (q1 w a) (U.image (q1 w)):= by
      rw [← Finset.image_insert,← us]
      intro hx;obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      have hyV : qb y:= by
        rcases Finset.mem_insert.mp hy with rfl | hu
        · exact ha.1
        · exact hU y hu
      exact hf (sf w hyV (ye ha.1) he ▸ hy)
    exact q2.unary (ui w ha) hne
      (fun hm=>hr ((s1 w ha.1).mp hm)) ih
  | @binary k t U a b d ha hb hab hf hra hrb tail ih =>
    have hU : ∀ x ∈ U,qb x:=fun x hx =>
      (qv tail.nlive x (Finset.mem_insert_of_mem hx)).1
    simp only [Finset.image_insert,su] at ih ⊢
    have hne : qn d (q1 w a) (q1 w b) ∉
        insert (q1 w a) (insert (q1 w b) (U.image (q1 w))):= by
      rw [← Finset.image_insert,← Finset.image_insert,← su]
      intro hx;obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      have hyV : qb y:= by
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact ha.1
        rcases Finset.mem_insert.mp hy with rfl | hu
        · exact hb.1
        · exact hU y hu
      exact hf (sf w hyV (x9 d ha.1 hb.1) he ▸ hy)
    have hm (v : q0) (hvV : qb v) (hv : v ∉ U) : q1 w v ∉ U.image (q1 w):= by
      intro hx;obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hx
      exact hv (sf w (hU y hy) hvV he ▸ hy)
    refine q2.binary (ui w ha) (ui w hb)
      (fun e=>hab (sf w ha.1 hb.1 e)) hne ?_ ?_ ih
    · intro hx;obtain ⟨h1,h2⟩:=hra ((s1 w ha.1).mp hx)
      exact ⟨h1,hm _ ha.1 h2⟩
    · intro hx;obtain ⟨h1,h2⟩:=hrb ((s1 w hb.1).mp hx)
      exact ⟨h1,hm _ hb.1 h2⟩
lemma sj (t : Nat) : (!Nat.beq t 0)=decide (0<t):= by cases t <;> rfl
def rs (v : List q0) (g : q0) : Bool :=
  !(up g v)&&!(Nat.beq g.1 0&&Nat.beq g.2 0)&&!(Nat.beq g.1 rx&&Nat.beq g.2 rx)
lemma xi {v : List q0} {g : q0} (hg : g ∉ v) (hp : qd g) :
    rs v g=true:= by
  have hm : up g v=false:= by
    cases e : up g v;rfl;exact (hg ((y5 g v).mp e)).elim
  have h0 : (Nat.beq g.1 0&&Nat.beq g.2 0)=false:= by
    cases e : (Nat.beq g.1 0&&Nat.beq g.2 0);rfl
    simp only [Bool.and_eq_true,Nat.beq_eq] at e;exact (hp.2.1 (Prod.ext e.1 e.2)).elim
  have h1 : (Nat.beq g.1 rx&&Nat.beq g.2 rx)=false:= by
    cases e : (Nat.beq g.1 rx&&Nat.beq g.2 rx);rfl
    simp only [Bool.and_eq_true,Nat.beq_eq] at e;exact (hp.2.2 (Prod.ext e.1 e.2)).elim
  simp [rs,hm,h0,h1]
def v7 (k t : Nat) (r : List q0->Bool) (v rest : List q0) (n : Nat) (c : Nat)
    (g : q0) (keep : List (List q0)) : Bool :=
  let d:=!Nat.beq t 0
  let base:=r9 d g|||c
  if Nat.beq n (k - t) then
    Nat.beq base rx&&rs v g&&r (g :: rest)
  else keep.any (fun h=>Nat.ble (n+h.length) (k - t) &&
    Nat.beq (base|||q9 d h) rx&&rs v g&&r (g :: (h++rest)))
def q12 (k t len : Nat) (r : List q0->Bool) (v : List q0) (c : y3) (a : q0) : Bool :=
  !(qa a) &&
    v7 k t r v (vs a v) (len - 1) (vr c (r9 (!Nat.beq t 0) a))
      (qx a) [[],[a]]
def yf (k t len : Nat) (r : List q0->Bool) (v : List q0) : Bool :=
  let c:=qz (!Nat.beq t 0) v
  v.any (q12 k t len r v c)
def sr (a b : q0) (spa spb : Bool) : List (List q0) :=
  if spa then (if spb then [[]] else [[],[b]])
  else (if spb then [[],[a]] else [[],[a],[b],[a,b]])
def xk (r : List q0->Bool) (v : List q0)
    (a b : q0) (ua ub na1 nb1 : Nat) (spa spb : Bool) : Bool :=
  (Nat.beq (ua&&&nb1) 0&&Nat.beq (ub&&&na1) 0&&!spa&&!spb &&
    (let g:=(a.1&&&b.1,a.2&&&b.2);rs v g&&r (g :: ug a b v))) ||
  (Nat.beq (ua&&&b.2) 0&&Nat.beq (ub&&&a.2) 0 &&
    (let g:=(a.1|||b.1,a.2|||b.2);rs v g&&r (g :: ug a b v)))
def u5 (k t len : Nat) (r : List q0->Bool) (v : List q0) (c : y3)
    (a b : q0) (sa sb : Nat) (spa spb : Bool) : Bool :=
  let rest:=ug a b v
  let m:=uc c sa sb
  (!spa&&!spb &&
    v7 k t r v rest (len - 2) m (a.1&&&b.1,a.2&&&b.2) [[],[a],[b],[a,b]]) ||
    v7 k t r v rest (len - 2) m (a.1|||b.1,a.2|||b.2) (sr a b spa spb)
def v1 {α : Type} (p : α->α->Bool) : List α->Bool
  | []=>false
  | a :: t=>t.any (p a)||v1 p t
lemma u6 {α : Type} (p : α->α->Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b=true) (hba : p b a=true) : v1 p v=true:= by
  induction v with
  | nil=>simp at ha
  | cons h v ih =>
    simp only [v1,Bool.or_eq_true]
    by_cases eqA : a=h
    · subst h
      exact Or.inl (List.any_eq_true.mpr ⟨b,(List.mem_cons.mp hb).resolve_left (Ne.symm hne),hab⟩)
    · have ha':=(List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b=h
      · subst h
        exact Or.inl (List.any_eq_true.mpr ⟨a,ha',hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))
def vt (k t len : Nat) (r : List q0->Bool) (v : List q0) : Bool :=
  if Nat.beq t 0&&Nat.beq len (k+2) then
    let u:=(zi v).2
    let acts:=v.map (fun a=>(a,u&&&r9 false a,rm a.1,qa a))
    v1 (fun x y=>xk r v x.1 y.1 x.2.1 y.2.1 x.2.2.1 y.2.2.1 x.2.2.2 y.2.2.2) acts
  else
    let d:=!Nat.beq t 0
    let c:=qz d v
    let items:=v.map (fun a=>(a,r9 d a,qa a))
    v1 (fun x y=>u5 k t len r v c x.1 y.1 x.2.1 y.2.1 x.2.2 y.2.2) items
def u1 : List q0->Bool
  | [a]=>rg a qc
  | _=>false
def v0 (k t : Nat) (v : List q0) (u b : List q0->Bool) : Bool :=
  let len:=v.length
  if Nat.blt (k+1) t||Nat.blt (k+2 - t) len then false else
    u1 v||(!Nat.beq t 0&&yf k (t - 1) len u v)||vt k t len b v
def xd : Nat->Nat->List q0->Bool
  | 0,_,v=>u1 v
  | k+1,t,v=>v0 k t v (xd k (t - 1)) (xd k t)
lemma xh {k t m : Nat} {v rest h : List q0} {g : q0} {opts : List (List q0)}
    {S : Finset q0} {r : List q0->Bool} (l : qy m t S)
    (hle : m ≤ k) (hp : qd g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g :: (h++rest)).Nodup) (he : (g :: (h++rest)).toFinset=S)
    (hr : r (g :: (h++rest))=true) :
    v7 k t r v rest rest.length (q9 (decide (0<t)) rest) g opts=true:= by
  obtain ⟨ht,hc⟩:=xg l
  rw [← he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length ≤ k - t:= by omega
  have cv:=q09 l he
  rw [q9,zm] at cv
  have cov : (r9 (decide (0<t)) g|||q9 (decide (0<t)) rest)|||q9 (decide (0<t)) h=rx:= by
    rw [← cv];ac_rfl
  have hav:=xi ha hp
  by_cases tight : rest.length=k - t
  · have hz : h.length=0:= by omega
    have hem : h=[]:=List.length_eq_zero_iff.mp hz
    subst h
    have ok : r9 (decide (0<t)) g|||q9 (decide (0<t)) rest=rx:= by
      simpa [q9] using cov
    simp only [v7,sj,tight,Nat.beq_refl,ite_true,ok,hav,Bool.and_true,Bool.true_and]
    simpa using hr
  · have hnt : Nat.beq rest.length (k - t)=false:= by
      cases e : Nat.beq rest.length (k - t);rfl;exact (tight (Nat.beq_eq.mp e)).elim
    simp only [v7,sj,hnt,Bool.false_eq_true,ite_false,List.any_eq_true,
      Bool.and_eq_true,Nat.ble_eq,Nat.beq_eq,hav,and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩
lemma x1 {c : y3} {a b : q0} (hc : sv c)
    (op : Bool) (h : r9 false (qn op a b)|||uc c (r9 false a) (r9 false b)=rx) :
    ((c.2.1&&&r9 false a)&&&(if op then b.2 else rm b.1)) |||
    ((c.2.1&&&r9 false b)&&&(if op then a.2 else rm a.1))=0:= by
  apply Nat.eq_of_testBit_eq;intro i
  by_cases hi : i<252
  · have hh:=congrArg (fun z : Nat=>z.testBit i) h
    clear h
    cases op <;> simp only [r9,qn,ite_false,ite_true,uc,qg,
      Nat.testBit_and,Nat.testBit_or,q5 _ hi,Nat.zero_testBit,
      Bool.false_eq_true,hi,decide_true] at hh ⊢ <;>
      cases ax : a.1.testBit i <;> cases ay : a.2.testBit i <;>
      cases bx : b.1.testBit i <;> cases byy : b.2.testBit i <;>
      cases um : c.2.1.testBit i <;> simp [ax,ay,bx,byy,um] at hh ⊢
  · have hge : 252 ≤ i:= by omega
    simp [Nat.testBit_or,Nat.testBit_and,hc.2.1 i hge]
lemma q1e {k r v c a b} (hc : sv c)
    (hlen : v.length - 2=k)
    (h : u5 k 0 v.length r v c a b (r9 false a) (r9 false b) (qa a) (qa b)=true) :
    xk r v a b (c.2.1&&&r9 false a) (c.2.1&&&r9 false b) (rm a.1) (rm b.1)
      (qa a) (qa b)=true:= by
  have heq : Nat.beq (v.length - 2) (k - 0)=true:=Nat.beq_eq.mpr (by omega)
  simp only [u5,v7,heq,ite_true,Bool.or_eq_true,Bool.and_eq_true,
    Nat.beq_eq] at h
  simp only [xk,Bool.or_eq_true,Bool.and_eq_true,Nat.beq_eq]
  rcases h with ⟨⟨ha,hb⟩,⟨hcov,hav⟩,hr⟩ | ⟨⟨hcov,hav⟩,hr⟩
  · have h0:=x1 hc false hcov
    have h1 : (c.2.1&&&r9 false a)&&&rm b.1=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢;exact hi.1
    have h2 : (c.2.1&&&r9 false b)&&&rm a.1=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢;exact hi.2
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · have h0:=x1 hc true hcov
    have h1 : (c.2.1&&&r9 false a)&&&b.2=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢;exact hi.1
    have h2 : (c.2.1&&&r9 false b)&&&a.2=0:=Nat.eq_of_testBit_eq fun i=>by
      have hi:=congrArg (fun z : Nat=>z.testBit i) h0
      simp only [Nat.testBit_or,Bool.or_eq_false_iff,Nat.zero_testBit] at hi ⊢;exact hi.2
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩
lemma zz {m t k : Nat} {U : Finset q0} {a : q0} {v : List q0}
    {r : List q0->Bool}
    (hv : v.Nodup) (hval : ∀ x ∈ v,qb x) (he : v.toFinset=insert a U) (hle : m ≤ k)
    (fresh : qx a ∉ insert a U) (ha : a ∉ qf) (l : q2 m t (insert (qx a) U))
    (ih : ∀ v : List q0,v.Nodup->v.toFinset=insert (qx a) U->r v=true) :
    yf k t v.length r v=true:= by
  let h:=s8 U [a];let rest:=qw [a] v
  have ah : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩:=vz (del:=[a]) (U:=U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn;change (h++rest).toFinset=U at eq
  have nn : qx a ∉ v:=fun hm=>fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : qx a ∉ U:=fun hm=>fresh (Finset.mem_insert_of_mem hm)
  have hnd : (qx a :: (h++rest)).Nodup :=
    List.nodup_cons.mpr ⟨fun hm=>nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (qx a :: (h++rest)).toFinset=insert (qx a) U:= by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]]:= by by_cases hm : a ∈ U <;> simp [h,s8,hm]
  apply List.any_eq_true.mpr;refine ⟨a,ah,?_⟩
  unfold q12;rw [sj,q0h]
  obtain ⟨hlen,hmask⟩:=q2b (decide (0<t)) hv hval ah
  rw [hlen,hmask];apply Bool.and_eq_true_iff.mpr
  have hna : qa a=false:= by cases es : qa a;rfl;exact (ha ((ri a).mp es)).elim
  exact ⟨by simp [hna],
    xh l.nlive hle (qv l.nlive _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
lemma yi {m t k : Nat} {U : Finset q0} {a b : q0} {d : Bool} {v : List q0}
    {r : List q0->Bool}
    (hv : v.Nodup) (hval : ∀ x ∈ v,qb x) (he : v.toFinset=insert a (insert b U)) (hle : m ≤ k)
    (hab : a ≠ b) (fresh : qn d a b ∉ insert a (insert b U))
    (hra : a ∈ qf->d=true/\a ∉ U) (hrb : b ∈ qf->d=true/\b ∉ U)
    (l : q2 m t (insert (qn d a b) U))
    (ih : ∀ v : List q0,v.Nodup->v.toFinset=insert (qn d a b) U->r v=true) :
    u5 k t v.length r v (qz (decide (0<t)) v) a b
      (r9 (decide (0<t)) a) (r9 (decide (0<t)) b) (qa a) (qa b)=true:= by
  let g:=qn d a b;let h:=s8 U [a,b];let rest:=qw [a,b] v
  have ah : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩:=vz (del:=[a,b]) (U:=U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn;change (h++rest).toFinset=U at eq
  have nn : g ∉ v:=fun hm=>fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U:=fun hm=>fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g :: (h++rest)).Nodup :=
    List.nodup_cons.mpr ⟨fun hm=>nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g :: (h++rest)).toFinset=insert g U:= by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]]:= by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,s8,ha,hb]
  have allow : h ∈ sr a b (qa a) (qa b):= by
    cases esa : qa a <;> cases esb : qa b <;> simp only [sr,ite_true,ite_false,Bool.false_eq_true]
    · exact opts
    · have hnb : b ∉ U:=(hrb ((ri b).mp esb)).2
      by_cases ha : a ∈ U <;> simp [h,s8,ha,hnb]
    · have hna : a ∉ U:=(hra ((ri a).mp esa)).2
      by_cases hb : b ∈ U <;> simp [h,s8,hna,hb]
    · have hna : a ∉ U:=(hra ((ri a).mp esa)).2
      have hnb : b ∉ U:=(hrb ((ri b).mp esb)).2
      simp [h,s8,hna,hnb]
  obtain ⟨hlen,hmask⟩:=q27 (decide (0<t)) hv hval ah bh hab
  unfold u5;dsimp only;rw [q0g,hlen,hmask]
  cases d with
  | false =>
    have na : qa a=false:= by cases es : qa a;rfl;exact (Bool.false_ne_true (hra ((ri a).mp es)).1).elim
    have nb : qa b=false:= by cases es : qa b;rfl;exact (Bool.false_ne_true (hrb ((ri b).mp es)).1).elim
    apply Bool.or_eq_true_iff.mpr;left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      xh l.nlive hle (qv l.nlive _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr;right
    exact xh l.nlive hle (qv l.nlive _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)
lemma zw {m t k : Nat} {U : Finset q0} {a b : q0} {d : Bool} {v : List q0}
    {r : List q0->Bool}
    (hv : v.Nodup) (hval : ∀ x ∈ v,qb x) (he : v.toFinset=insert a (insert b U)) (hle : m ≤ k)
    (hab : a ≠ b) (fresh : qn d a b ∉ insert a (insert b U))
    (hra : a ∈ qf->d=true/\a ∉ U) (hrb : b ∈ qf->d=true/\b ∉ U)
    (l : q2 m t (insert (qn d a b) U))
    (ih : ∀ v : List q0,v.Nodup->v.toFinset=insert (qn d a b) U->r v=true) :
    vt k t v.length r v=true:= by
  have ah : a ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1:=yi hv hval he hle hab fresh hra hrb l ih
  have e' : v.toFinset=insert b (insert a U):= by rwa [Finset.insert_comm b a]
  have hf : qn d b a ∉ insert b (insert a U):= by rwa [s0 d b a,Finset.insert_comm b a]
  have ht : q2 m t (insert (qn d b a) U):= by rwa [s0 d b a]
  have h2:=yi hv hval e' hle hab.symm hf hrb hra ht (by simpa only [s0 d b a] using ih)
  unfold vt;split
  · rename_i cut
    simp only [Bool.and_eq_true,Nat.beq_eq] at cut
    obtain ⟨rfl,hvlen⟩:=cut
    have hlen : v.length - 2=k:= by omega
    have hc:=ru false hval
    have hcov2:=(q2c v).2
    let f:=fun x=>(x,(zi v).2&&&r9 false x,rm x.1,qa x)
    have na : f a ∈ v.map f:=List.mem_map_of_mem ah
    have nb : f b ∈ v.map f:=List.mem_map_of_mem bh
    exact u6 _ na nb (fun e=>hab (congrArg Prod.fst e))
      (by simpa only [f,hcov2] using q1e hc hlen h1)
      (by simpa only [f,hcov2] using q1e hc hlen h2)
  · rw [sj]
    let f:=fun x=>(x,r9 (decide (0<t)) x,qa x)
    have na : f a ∈ v.map f:=List.mem_map_of_mem ah
    have nb : f b ∈ v.map f:=List.mem_map_of_mem bh
    exact u6 _ na nb (fun e=>hab (congrArg Prod.fst e)) h1 h2
lemma xq {m t S : Nat} {s : Finset q0} {v : List q0} {u b : List q0->Bool}
    (h : q2 m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset=s)
    (hu : ∀ w,w.Nodup->∀ l ≤ S,q2 l (t - 1) w.toFinset->u w=true)
    (hb' : ∀ w,w.Nodup->∀ l ≤ S,q2 l t w.toFinset->b w=true) :
    v0 S t v u b=true:= by
  have size:=xg h.nlive
  have hval : ∀ x ∈ v,qb x:=fun x hx =>
    (qv h.nlive x (he ▸ List.mem_toFinset.mpr hx)).1
  rw [← he,List.toFinset_card_of_nodup hv] at size
  have hcond : (Nat.blt (S+1) t||Nat.blt (S+2 - t) v.length)=false:= by
    have h1 : Nat.blt (S+1) t=false:= by cases e : Nat.blt (S+1) t;rfl;have:=Nat.blt_eq.mp e;omega
    have h2 : Nat.blt (S+2 - t) v.length=false:= by cases e : Nat.blt (S+2 - t) v.length;rfl;have:=Nat.blt_eq.mp e;omega
    simp [h1,h2]
  unfold v0;dsimp only;rw [hcond];simp only [Bool.false_eq_true,ite_false,sj]
  cases h using q2.byCases with
  | stop =>
    have p : v.Perm [qc]:=List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    rw [List.perm_singleton.mp p];simp [u1,(rf qc qc).mpr rfl]
  | @unary m t U a _ hf hr tail =>
    apply Bool.or_eq_true_iff.mpr;left
    apply Bool.or_eq_true_iff.mpr;right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp,zz hv hval he (by omega) hf hr tail ?_⟩
    intro w hn hs;exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d _ _ hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr;right
    apply zw hv hval he (by omega) hab hf hra hrb tail
    intro w hn hs;exact hb' w hn m (by omega) (hs.symm ▸ tail)
lemma y9 {m t : Nat} {S : Finset q0} (h : q2 m t S) (k : Nat)
    (hk : m ≤ k) (v : List q0) (hv : v.Nodup) (hs : v.toFinset=S) : xd k t v=true:= by
  induction k generalizing m t S v with
  | zero =>
    have hm : m=0:= by omega
    subst m;cases h using q2.byCases
    have p : v.Perm [qc]:=List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    rw [List.perm_singleton.mp p];simp [xd,u1,(rf qc qc).mpr rfl]
  | succ k ih =>
    rw [xd]
    apply xq h hk hv hs <;> exact fun w hn l hl hh=>ih hh hl w hn rfl
def qs (k t : Nat) (v : List q0) : Prop :=
  ∀ m ≤ k,¬ q2 m t v.toFinset
lemma yy {k t : Nat} {v : List q0} (hv : v.Nodup) (hc : xd k t v=false) :
    qs k t v:= by
  intro m hm h;exact Bool.false_ne_true (hc.symm.trans (y9 h k hm v hv rfl))
lemma xv {k t : Nat} {v : List q0} {u b : List q0->Bool} (hv : v.Nodup)
    (hu : ∀ w,u w=false->qs k (t - 1) w)
    (hb : ∀ w,b w=false->qs k t w)
    (hc : v0 k t v u b=false) : qs (k+1) t v:= by
  intro m hm h
  have hu' : ∀ w,w.Nodup->∀ j ≤ k,q2 j (t - 1) w.toFinset->u w=true:= by
    intro w _ j hj r;cases e : u w;exact (hu _ e j hj r).elim;rfl
  have hb' : ∀ w,w.Nodup->∀ j ≤ k,q2 j t w.toFinset->b w=true:= by
    intro w _ j hj r;cases e : b w;exact (hb _ e j hj r).elim;rfl
  exact Bool.false_ne_true (hc.symm.trans (xq h hm hv rfl hu' hb'))
def q2z (mult : Nat) (a : q0) : Nat :=
  let x:=((a.1 % 1048573)*mult+a.2 % 1048573+317) % 1048573
  (x*x*x) % 1048573
def q0c (mult : Nat) : List q0->Nat
  | []=>0
  | a :: l=>q2z mult a+q0c mult l
def uf (mult : Nat) (v : List q0) : Nat :=
  q0c mult v % 1048573
def q6 : Nat->Nat
  | 0=>0x76543210 | 1=>0x25613740 | 2=>0x45670123 | 3=>0x16520473 | 4=>0x43076215 | 5=>0x13025746 | 6=>0x70345126 | _=>0x20316475
def q2w : Nat->Nat
  | 0=>0x4600408a1100140010c06007841005000400020aa0003e0070160003c0220160e804400054000380070660bc3640400a0bc044330110c8014000c40080782f0090b80140001c0b00242b0050002a0070120002800701a098044000940500680008c0182281001e0800140007c0780680101d0700440106d0400581006506005804009058024010550500580701103012410002040044010090300e40d002008074040050000a00901e0100880100a
  | 1=>0xbc0481821500407814009000820070950008007f01a17c074260090980147b011004564180490085a4021610087643200e040744110020b8094001c40440782e17d0b86e4610120b86c4100121a8044000880006806701e17c02400194190078040210b8624610060000203217d004048001741700780c00a0b85a42f00e0b85840c00e0b85641000e0b85441400e0b81242e0390b80842e0090b84e4180061300842e0110b84a4490060000402b021
  | 2=>0xc60010a9008c44001fc004744003042fc074002fc040068002f4274068002ec01c1f4002e42e0068000d80d8194b5011008038042cd210038002c4210068002bc2b80686101d080024022ad010058a90092a0058a701100001015009008a4450016008a248c016008a04110162780249d0160500140226d01003802265260038850110085442e062230188320622480442e00a0ac1880223d0b80488d009230048002140bc188890110bc02887009
  | 3=>0x418024010aa0082a40240d1240782f036214024023fd1b0068023f50101f8023ed010068f90ba124024363d9008f640005012802408049008f246c0023001083606d0d8564561b1008ec4051b23a8024db016008e8401016008e64031b2008e440336e0b86789217d380024df0120b8018dd0090780480236d050018023650040382e042130108320420ac108920053480142b00a3400144c00a0402a41001d3302e8a7009020c94023250001e00231d
  | 4=>0xd94654400e0206c436005021424140020b86488f0214f8028043252a00293b00a4e8044a701d2a0108363252a02e85f3254d0028040490d80e43604917c0e45f0490486c45f4b54b00080017c0e8028004a401c1547b00a498028010490200e523039034018c000a0800291f00a06c0451d00a1580442600a1c00291900a0011800c01e2300291500a230044920a90c80d82c00a0d40290f00a001060024350000c00242d428078a70124200240403a
  | 5=>0x17d0d58400a020f64013d91240157a00a0617d8002900017e007065000190005ec01c1b40006c2480488901245c0480d0122600281400a0d88543601d0d9704000605b8048020494980496b0120040e4e90123680481023e350048ce0122146c41005254c048970121440486a0120c8048300120115c4000400c40442b0520102255700a0045855500a1500155300a0054255100a0105840c24a538028df0115300280123d2740285c0a91708540d032
  | 6=>0x170039c500e0783649d00e01c585c100e0081f5b100e350038ce00e2180383300e1040383500e0c00381100e0c47645606d6d00085c01d274009b10020345f4da00225c008780020c00095c0496a80e4000343d94241206d04856579006664049230120057495b0060c45f59f006010bf4160124d001892006340018d2006078029050060202a4070213dc018970060601e8840063680188c07a130018320061400182b0060057043100510c01408571
  | 7=>0x7140580027400204014021001c50023da124028005640a8f64490421240740306e7e805807159001f80071b1001640b80620017217e00e00805867016378058dc0166c4058da0167b0058df00933c058ce01625c058900162180588401621419478016788058500110c005970065778038010650d8c98a7052008c980231e29c029d704200008000628214c940074c1380740064c0019600065c008c4800684001cc00901d5d00380726d72003861011
  | 8=>0x4040680d01a0601fa0401a25c0686701a370069b101a0600688601a8f00684907a7f80684901a004b9a3701a000090df01a004068c601a6280698901a8c00680140d8b806a0100560c06a2b01a60c0762901a2e00141c01a7780694401a890068015d17140680c01a8800680c0c53680687801a360068cf01a868069830093380683001a0440682c01a104068003380115c80757100067000414015749f801656c059590164a4048083da004f684e016
  | 9=>0x18468000440183180621685c07a2d01e01d5c8074369ec05a7b00a29c0799f01e9e0078040952a007a75006184079d701e00c228070229c0078022fd9b80780209510c0181040e3680787801e25c07a6701e1840158301e070078b801e7780781601e51007a1a01e014bf97b01a7640683607e0d80685f01a01233804866040259f801a564068002100057086201a940069d701d70c068032fe7e806a0101a0200680207e00a2d80201a
  | _=>0
def qk : Nat->Nat->Nat
  | 8,0=>1343
  | 8,1=>349
  | 8,2=>6
  | 9,0=>602
  | 9,1=>378
  | 9,2=>41
  | 10,0=>64
  | 10,1=>84
  | 10,2=>43
  | 10,3=>8
  | 11,0=>5
  | 11,1=>6
  | 11,2=>6
  | 11,3=>6
  | 11,4=>1
  | _,_=>0
def q3y : Nat->Nat->Nat
  | 8,0=>992
  | 8,1=>227
  | 8,2=>2
  | 9,0=>488
  | 9,1=>283
  | 9,2=>35
  | 10,0=>64
  | 10,1=>84
  | 10,2=>43
  | 10,3=>8
  | 11,0=>5
  | 11,1=>6
  | 11,2=>6
  | 11,3=>6
  | 11,4=>1
  | _,_=>0
def q3x : Nat->Nat->Nat
  | 8,0=>1335
  | 8,1=>333
  | 8,2=>6
  | 9,0=>602
  | 9,1=>378
  | 9,2=>41
  | 10,0=>64
  | 10,1=>84
  | 10,2=>43
  | 10,3=>8
  | 11,0=>5
  | 11,1=>6
  | 11,2=>6
  | 11,3=>6
  | 11,4=>1
  | _,_=>0
def q3w : Nat->Nat->Nat->Nat
  | 8,0,0=>0x132ff0002eff000fbff00029ff00030ff00084ff00081ff00089ff00225bf0010aff000cdff00171ff00083ff00214bf00211bf00135ff002597f0016cff00237bf0021cbf0021abf0012afe00141ff00142ff0022bbf00190ff00018bf00191ff00003ff0019dff000feff00143ff00215bf00212bf00210bf00250bf00129fe0000aff0015dff00100ff0023abf0021ebf0019cff00144ff0006a7f0015eff0013eff00002ff00060ff0016eff0007fff0022cbf00055ff00009ff00011ff00065ff000c8ff0001b7f000b8bf00001ff000d5ff0002fff000d7ff00000ff
  | 8,0,1=>0x1d6ff00131ff000cbff00024ff00153ff00041ff000ceff00025ff0008aff00193ff000ccff0020fbf0010bff00026ff000efff001a2fe00181ff000f0ff000f0fb0017fff00203ff0017eff000f1ff001fbff00226bf0013aff0015aff00066ff0006cff000dcff00114ff00048ff00139ff00161ff0022abf00146ff00136ff00046ff000d0ff00194ff000caff0008cff00045ff000d1ff0008fff0010dff000dbff00149ff00105ff00228bf00160ff0019fff000daff00148ff00195ff00082ff00172ff000c9ff00027ff00088ff00069ff0008bff0004aff00028ff
  | 8,0,2=>0x84009bf8402fbf84011bf001c7ff00062ff001fcff001cbff00057ff001cdff001c9ff00004ff001c6ff0005fff001feff001f0ff00040ff001f2ff0006bff001caff00063ff000bdff0003aff001ffff0003dff001c8ff000beff00113ff0003eff0020ebf00109ff0003bff001d3ff000c1ff00159ff00064ff00044ff000f3ff000b2bf0005cff000c6ff00068ff00130ff00110ff00127fe0002bff00059ff0008eff0010cff000cfff0002cff0008dff00170ff00087ff00223bf0010fff0002dff000c2ff001a4fe0016aff0012fff000c3ff00138ff000c4ff001d4ff
  | 8,0,3=>0x380adf0780abf3500afd0600abf06c0a7f0500adf2e00abf1940aef0480adf62c09fd57c11ef08c6a7f62cd5fd1f86a7f57cd7ef1a8017f1a8097f1a82f7f1a8117f2d944bf1a8995f265b1d708612bf77c9fdf2642fdf26411df8ba12bf2649adf2d801bf2d809bf94612bf6f470f76f42ff76f411f76c42ff76c411f790612bf6c471f784801bf84809bf8482fbf84811bf25d44df1aa103f840999f841b1b72a8acb79ea10bf25c98df78c2fdf78c11df8ba10bf2b0adf72a801bf2a809bf3d210bf2b090f72b02ff72b011f76dc2ff76dc11f790610bf1b4bcfe84001bf
  | 8,0,4=>0xfc1b7f06d5d7f06c2f7f06d007f06e4e3f06e055f35065fd06cd47d35060fd19460ef0a87e7f3516efd06e2c3f19455ef9ac1b7f1953eef350fefd06c145f06cb83f06c657f06c656f3fc1b7f3515efd06c027f06c607f9681b7f06c7f7f06c125f06c557f35144fd03944df07944bf57c0aef06c6a7f06c097f1a8c87f1a8145f1a8b83f1a8657f06d5f6f1a80a7f26465df06e123f2640adf2e212bf26413df2e0999f2e1b1b7051b1d784865bf06c995f8480abf78c65df06e103f78c0adf2e210bf2e009bf1b46efe2e1e39f038acd7078acb784065bf06de35f8400abf
  | 8,0,5=>0x5002df038fedf910b8bf02cedfe078febf2e0149f2e04fb70504fd707802bf4ec60fe950b8bf02d29fe16129fe2e002bf4ec55fe8ecb8bf02c0cfe2e0129f02c55fe93c09bf93809bf350d5fd06cc87f1f81b7f8b009bf5b4d5fb078d5bf070b8bf13ce7f713c2ff713c60f70502fdf05060df0799cbf038d5df3e0b8bf02d28fe1342ff702c60fe2e02fbf2e060bf81c65df93c65bf35009fd8e8d5bf7a4d5df06cd57f06cfe7f07865bf03865df06c1e3f06c0e5f5b460fb06065bf4441b7f5b4fefb05065df2e065bf7ac65df19411ef7ac60df04865df35055fd06c183f
  | 8,0,6=>0x9ecb8bf038a5df0722ebf13495f713cd3f702d68fe13d21f705163df13c75f7050fedf4ed3cfe2e0febf940b8bf94009bf078149f0784fb79f8b8bf038e4df070f8bf02cecfe2e0f9bf25090f74ed5cfe96c0e5f7d04fd79184fb795c149f4ed4dfe9ccb83f03810df02d2efe9a01e3f94cb8bf02d2bfe03802df03860df2e055bf0604fb787cb8bf02c73fe03855df07860bf13ce8f707855bf0484fd7900b8bf05055df9f0b8bf13caff7050e2df9062ebf078f5bf70c90f737cd3f702d66fe978145f8604fb779c4fd7884149f02d20fe9c81e3f13d62f79a8b83f05016df
  | 8,0,7=>0x1a8125f1a8557f6b055fe2a80abf8e210bf1b40cfe840129f1b455fe6f455f777c0adf06212bf6c475f76c455f72d855bf2d80abf049b1d78fe12bf26416df26455df84055bf048acd786e10bf1b473fe25c55df25c0adf06001bf854febf790fedf1a8fe7f04811df1e401bf8b001bf06c017f0a9117f08c1b7f04802df048fedf91018bf01d1efe06002bf060febf8f401bf85409bf854c8bf9415dbf1e409bf8b018bf04813df04860df2e0c8bf2e15dbf4a409fe050e6df134def713ce0f713d17f71354ff705119df13460f7050e9df13455f78b0b8bf7ac11df13c55f7
  | 8,0,8=>0x7807fdf6d87ff78b011bf06c117f4fc11f777811df0487fdf14541f7048b0df14460f79ec18bf048a5df0862ebf14495f7144d3f71454bf714551f704919df06060bf01d2cfe06051b78b418bf94c18bf01d02fe048e6df90e2ebf060f7bf6f071f725071f701d65fe970125f061bbb792051b7880129f01d20fe9c8183f01d2efe9a0183f04816df95418bf01d2afe1612afe01c60fe8f818bf01c08fe060129f8ac11bf01d9dfe060d7bf90c18bf01d1dfe1442ff706055bf0f1117f14455f76b855fe7a8d7df4fc55f701c55fe04855df06144bf62c0afd4446a7f1a87f7f
  | 8,0,9=>0x7082ff770811f714c2ff714c11f790a26bf14c72f789801bf89809bf8982fbf89811bf16028fd28936df0aa5f7f08e5f7f14c2ef76cc28f76cc2ef714c82f79c07e7f27429df06c287f84428bf76828df6c828f769828fe55c28ef06c297f76829df84429bf55c29ef1e402bf1e460bf9f22cbf4fd40f77ac02df57c60ef6e460f76ac60fe8e460bf7a060df62c60fd2496ef72487ff70722cbf818a5df8ba2cbf7ace6df94a2cbf24893f72482ff74fc2ff790e2cbf4fcd3f78b02fbf7ac2fdf0aa5a7f24811f78002fdf8702fbf6fc2ff78dc11bf78011df6d811f78dc7fbf
  | 8,0,10=>0x3b811fb160cdfd6e0cdf70348cef9d47e7f01c8bfe004cdfd06c8b7f2e08bbf0508bdf13c8bf702c8bfe1948bef0488bdf36028fd05c28fd36428fd62028fd9d07e7f8ce26bf14c54f714c8bf727428df27488df27445df2748bdf14c28f720045ef77027df61828fd06c277f76827df84427bf55c27ef06028bf35828fd2fc28fd07828bf03828df13428f74ec28fe35028fd5b428fb1e028fd14428f760c28fd01c28fe2e028bf05028df13c28f702c28fe19428ef04828df11c28fd9e626bf288a3df2742fdf27411df8ba26bf2749edf2a001bf2a009bf94e26bf70870f7
  | 8,0,11=>0x62c27fd2a827bf77c27df2d827bf25c27df8d818bf14452f71a8277f26427df84027bf0488fdf1442ef777011df03827df07827bf35027fd78427df07888bf03888df35088fd06088bf3f1117f06c887f05088df2e088bf3f01b7f5c889fb78488df3f411fb78489df0bc89fb04888df22045ef03445ef08cfc7f03845df07845bf35045fd03845cf24445ef06045bf06c457f05045df2e045bf19445ef04845df0aa617f77045df06027bf79827df360cdfd2208cef22c89fb0608bbf9d1117f3508bfd0788bbf0388bdf4ec8bfe1348bf79b81b7f1448bf7654cdfd6e08bf7
  | 8,0,12=>0x350f0fb9e01b7f5b4f0fb06e0c7f350f0fd350f0f982c0a7f5580aef1a9557f2d8efbf2a8efbf078efbf06d557f3bcf0fb7ecf0fb808f0fb5f4f0fd5f4f0f93c045fb08cf0fb55809ef638f0fb5f42efd004f0fb3c009fb2e0efbf06cef7f160f0fb0bcf0fb5f411fd3c011fb060efbf92cb8bf1344ef7958b8bf4ec4bfe9bc1b7f81827df8b027bf27427df8bc18bf01c4bfe57c27ef84827bf78c27df8d0b8bf13c50f7858b8bf02c4cfe9941b7f19466ef06cd17f050d1df2e0d1bf194d1ef05029df2e029bf19429ef85009bf84409bf964097f1e427bf7ac27df19427ef
  | 8,0,13=>0x26c9cdf1bc2ff71bc11f7914b2bf1bc70f72c801bf2c809bf2c82fbf2c811bf26d10df0aa5d7f08e5d7f1bc2cf761c2cfd6d42bf76d42cf71bc8bf776411df01da4fe68da4fe061d4bf060c3bf9dd117f41c0afb1a9067f84106bf2d906bf848c2bf78cc2df060c2bf89906bf06106bf750c3fb41c11fb024c3fb06cc27f2e0c2bf050c2df2e106bf07906bf06d067f0bcc3fb048c2df9b66b7f2fc25fd92801bf07824bf35024fd2e024bf06c247f06024bf9b47e7f61425fd83c24bf83c25bf69409fe4eda2fe3bda2fe07a02bf038f0df038f0db079fbbf078f0bf078f0bb
  | 8,0,14=>0x497bdf0601abf0611abf060a6bf0483ddf061ffbf8c401bf8c402bf8383abf2e0eabf0517bdf03834df03924df07876bf2e11bbf07820bf07915bf07877bf06c637f05063df2e063bf19463ef06d597f06c647f06c2c7f06e0d7f9f4b8bf079ffbf9f41b7f9f46a7f2d9ffbf9f610bf934f0fb3c027fb5f028fd89827bf26c27df1bc2bf72a027bf28827df05027df2e027bf04827df8b02bbf6c02bf749927fe16127fe2c802bf49860fe0e65d7f60c2cfd88c2fbf1442bf701c2bfe06c2b7f2e02bbf0782bbf13c2bf702c2bfe3502bfd0602bbf26c2fdf26c11df8c8b2bf
  | 8,0,15=>0x6019bf0781fbf2c8b3bf2a0a9bf82cd17f1e47abf06022bf060b5bf04832df04978df2e01dbf2e0bbbf07822bf0787cbf05036df05175df03838df03923df06c407f06df97f1a86b7f2d8b7bf2a8abbf82c277f55827ef2c827bf2a08bbf8382fbf6d02ff71e4bdbf06dcf7f0497adf
  | 8,1,0=>0x2e1b1b7051b1d706c995f06e103f2e1e39f038acd7078acb706de35f1a8995f265b1d71aa103f840999f841b1b72a8acb7000b3bf000a9bf0007abf0006b7f000b7bf000abbf000637f0017adf0020ebf000eabf000b2bf00127fe0010c7f001897d00223bf001a4fe00180fd001ce7d001537f0020fbf001a2fe00181fd000f0fb00226bf0022abf00228bf000277f00225bf00214bf00211bf002597f000d17f00237bf0021cbf0021abf0012afe0022bbf00018bf00215bf00212bf00210bf00250bf00129fe0023abf0021ebf0006a7f0022cbf0001b7f000b8bf00000ff
  | 8,1,1=>0x9a0183f060129f0bcd7eb444183f1a8125f0f18b7d840129f0f0aa3f049b1d7444b63f444975f048acd708c793f08d5d6f00409f98209fdb7b0e2db078149f0784fb771090f396c0e5f7d04fd79184fb795c149f9ccb83f9a01e3f4440e5f0604fb70484fd74441e3f2b8d3f3978145f8604fb779c4fd7884149f9c81e3f9a8b83f2e0149f2e04fb70504fd72e0129f0f01e3f004d5f967009f906c1e3f06c0e5f0bc11eb06c183f670d5f906e4e3f06e055f06cd47d0bc60eb06e2c3f06c145f06cb83f06c656f06c125f06c477d1a8145f1a8b83f06d5f6f06e123f2e0999f
  | 8,1,2=>0x3e82b7b0182b7b9d0d87d5a811eb1f9ce7d309ce7d4cc287d1f8c27d08d536f078243f74409f954c246f034246f60409f9038f0db078f0bb350f0f908df86f3bdf86f08cef6f5f4f0f9818275f8b0273f274275f57c276f848273f78c275f1e4273f62c277d2a8273f77c275f2d8273f25c275f038275f078273f350277d078883f03845cf060273f360287d050d15f2e0d13f194d16f7ac275f194276f264275f840273f784275f798275f360cd7d770275f768275f844273f55c276f1f99a7d16141ed7b0a5db06051b770071f3970125f061bbb792051b7880129f9c8183f
  | 8,1,3=>0x108276f280277d0cc275f07c273f280637d064273f5cc275f2e4273f108636f5d8275f5e4275f558276f2c8273f1f8bd7d0381f9f1341fb74ec1fbe3501fbd5b41fbb08c1f3f050635f2e0633f194636f2a0273f898273f3c0277b7dc276f3bc246f288275f754277d26c275f68c2b7b1f9897d7bc11eb4302b7b
  | 8,2,0=>0x1897d001ce7d
  | 9,0,0=>0x1ffff000efff00024ff000c2ff0002bff000b2bf00110ff0002cff001d4ff000c3ff000cbff00025ff001fbff000f0ff000f0fb00045ff00088ff00028ff0008bff0004aff000d1ff00069ff0008fff00089ff000c9ff00195ff000cdff00172ff0008cff00226bf00136ff0002eff00082ff00029ff0016cff0016eff0022cbf00009ff00065ff0001b7f0007fff00141ff0019dff000d7ff00001ff000feff00190ff00003ff00100ff00191ff00011ff00002ff00055ff000c8ff0015dff0000aff0019cff000d5ff0002fff00060ff00144ff0006a7f00212bf00210bf
  | 9,0,1=>0x2e02fbf2e011bf0fc09ff54809ff0bc09ff18009ff06c65ff05065df2e065bf0fc65ff350d5ff08c65ff08c1b7f5b409ff35009fd1f865ff35011ff00465ff19409ff19460ff0bc65ff19411ff19411ef06c145f06cb83f06c657f06c656f0fc1b7f350d5fd1f81b7f19460ef06c017f06c097f06c2f7f06c117f06c0aff06c0a7f31c0aff0500adf2e00abf1940aff1940aef57c09ff1a8097f84809bf84009bf08c0aff0340aff1f80aff0180aff0040aff0240aff0bc0aff0440aff1a80aff1a80a7f2640adf8400abf00027ff000bdff0003dff0003aff001caff00063ff
  | 9,0,2=>0x8d00ff9ac02ff00c02ff3fd00ff3fcfeff2fcfeff0e4feff08d91ff00411ff08cfeff004feff644feff3f8c8ff5bcfeff9ac2fff160feff3fc01ff08c60ff0bc55ff00801ff00460ff0082fff0bcfeff9ac11ff2fc11ff00811ff3f811ff08c55ff06001bf00455ff3f809ff67001ff08cc8ff024c8ff57409ff17409ff3fc09ff24409ff00809ff5bc09ff06009bf15409ff18011ff2e0149f2e04fb70504fd7070b8bf0389fdf0502fdf05011df8b8b8bf050e2df07801bf07809bf3e0b8bf13490f71342ff713411f713c2ff713c11f7904b8bf13cd3f72e001bf2e009bf
  | 9,0,3=>0xa02eff20828ff0a029ff0bd6cff00c2fff16100ff3fc02ff3fc60ff1e060ff00860ff1f96eff4fc2ff716060ff0a860ff18460ff3e87fff7ac60df1f860ff0bc60ff3e811ff6782fff1f87fff0447fff63011ff60c11ff4f411ff0482fdf04811df8b818bf048a5df1442ff714411f790c18bf14471f70602fbf06011bf99811ff60811ff16011ff44455ff14455f71f855ff47011ff16055ff11c11ff15855ff358d7ff11c60ff0a855ff0a9117f64811ff15411ff4440aff1f40aff0480adf1540aff62c11ff1a8117f84011bf26411df6c411f72b011f700590ff00c01ff
  | 9,0,4=>0x3445ff03445ef1f845ff01845ff00445ff02445ff0bc45ff04445ff08c45ff32445ff1142eff01827ff65427ff33427ff5c827ff23027ff3608bff2208bff22c45ff1f88bff10c11ff08c8bff40c09ff1608bff36011ff6548bff22ccdff5c88bff22c8cff0a88bff9d07e7f7e811ff0048bff22c09ff0bc8bff22c11ff36028ff36028fd22028ff11428ff22c28ff12428ff1f827ff27427df20027ff09c2eff20827ff09c29ff05c28ff05c28fd08c28ff03428ff16028ff16028fd01428ff0a828ff01828ff00428ff02428ff0bc28ff04428ff1f828ff14c28f720028ff
  | 9,0,5=>0x3bc2fff3bc11ff3f827ff09c45ff03827df07827bf5b427ff35027fd22027ff24427ff3e827ff09c28ff06027bf47027ff5bc27ff22c27ff9ac27ff63c27ff17427ff65401ff0044aff09c4aff06c27ff06c277f1080aff05027df2e027bf19427ff19427ef34409ff34427ff02429ff3fc27ff5ac27ff00827ff18027ff5c82fff16069ff09c69ff44427ff2800aff04827df15427ff09c0aff23c11ff23c27ff0142eff03427ff22427ff08c88ff08cfc7f74809ff1f888ff16c11ff00488ff22009ff5c888ff22089ff0bc88ff22011ff22045ff22045ef08c27ff32427ff
  | 9,0,6=>0x2427ff0bc27ff04427ff9ac2bff5502bff2c82fbf1f910ff0a82cff1602bff0142bff0a82bff0182bff0042bff0242bff0bc2bff0442bff1bc2bf75602bff0ac2cff22c2bff93011ff61011ff060c2bf41855ff4180aff5a42fff5a411ff30828ff4182fff41811ff750c2ff308c3ff30801ff30809ff3082fff30811ff3fc24ff3f824ff08ccbff08c25ff08c24ff03424ff00424ff02424ff0bc24ff04424ff22024ff32c24ff09025ff83009ff55809ff55809ef078efbf55465ff06d557f5540aff55401ff55409ff3bc45ff7ecefff3bcf0ff3bcf0fb3bc01ff3bc09ff
  | 9,0,7=>0x10827ff28027ff28024ff55427ff2802bff41827ff3f045ff9d028ff0bc3aff7b82fff82860ff06019bf0443dff0f03dff93411ff08c3aff0e43aff72801ff824feff0781fbf02463ff06c63ff06c637f83409ff9f40aff3bc27ff09c24ff3f027ff10845ff7e827ff10828ff30827ff09c2bff9b827ff28028ff74827ff28045ff40c27ff16828ff00427ff
  | 9,1,0=>0xefff00024ff000c2ff0002bff000b2bf00110ff0002cff001d4ff000c3ff000cbff00025ff001fbff000f0ff000f0fb00045ff00088ff00028ff0008bff0004aff000d1ff00069ff0008fff00089ff000c9ff00195ff000cdff00172ff0008cff00226bf00136ff0002eff00082ff00029ff000d17f0016cff0016eff0022cbf00009ff00065ff0001b7f0007fff00141ff0019dff000d7ff00001ff000feff00190ff00003ff00100ff00191ff00011ff00002ff00055ff000c8ff0015dff0000aff0019cff000d5ff0002fff00060ff00144ff0006a7f00212bf00210bf
  | 9,1,1=>0x6009bf11c09fd2e0149f2e04fb70504fd7070b8bf0389fdf0502fdf05011df8b8b8bf050e2df07801bf07809bf3e0b8bf13490f71342ff713411f713c2ff713c11f7904b8bf13cd3f72e001bf08c1e3f2e009bf2e02fbf2e011bf05065df2e065bf08c1b7f35009fd19411ef06c145f06cb83f06c657f06c656f0fc1b7f350d5fd1f81b7f19460ef06c017f06c097f06c2f7f06c117f06c0a7f0500adf2e00abf1940aef1a8097f84809bf84009bf1a80a7f2640adf8400abf00027ff000277f000bdff00019bf0003dff0003aff001caff0001fbf00063ff000637f001ffff
  | 9,1,2=>0x16028fd1f8287f14c28f7174277f09c4a7f050275f2e0273f194277f194276f344097f344277f008277f180277f09c697f048275f154277f09c0a7f23c277f224277f220457f324277f654277f334277f5c8277f230277f3608b7f360287f360287d274275f200277f09c2e7f208277f09c297f00860fb4fc2ff77ac60df0bc60fb0bc60ef0bc60eb0482fdf04811df8b818bf048a5df1442ff714411f790c18bf14471f70602fbf06011bf14455f716055ef0a9117f5bc11ef0480adf11c0afd1a8117f84011bf26411df6c411f72b011f70e4fefb00460fb0bcfefb06001bf
  | 9,1,3=>0x182b7f0182b7b1f82b7f1bc2bf79b82b7f060c2bf1f8c27f1f8c27d30828fd034247f034246f3f0247f55809ef078efbf06d557f08cef7f08cef6f3bc45ef3bcf0fb3f8277f09c457f03827df07827bf35027fd038275f078273f5b4277f350277d220277f244277f3e8277f09c287f06027bf060273f470277f5bc277f22c277f9ac277f63c277f06c277f1080aef05027df2e027bf19427ef3fc277f5ac277f444277f2800afd04827df034277f08cfc7f74809fd22045ef08c277f03445ef08c457f018277f1f88b7f9d07e7f7e811ef36028fd1f8277f27427df05c28fd
  | 9,1,4=>0x108277f280277f28024fd554277f2802bfd418277f5d811df06019bf0341fbf0781fbf024637f06c637f3f0277f10845ef9b8277f28028fd7e8277f10828ef3bc277f09c247f40c277f16828fb748277f28045fd308277f09c2b7f2c82fbf
  | 9,2,0=>0x182b7b1f8c27d034246f08cef6f038275f078273f350277d060273f050275f2e0273f194276f048275f360287d274275f0bc60eb2e0149f2e04fb70504fd708c1e3f06c145f06cb83f06c656f000277f00019bf0001fbf000637f000b2bf000f0fb00226bf000d17f0022cbf0001b7f0006a7f00212bf00210bf
  | 10,0,0=>0x10827ff28027ff0a82bff5a411ff08c24ff55409ff08c27ff03427ff1f827ff01827ff00427ff02427ff0bc27ff04427ff22027ff09c45ff22c27ff09c28ff1f82fff0082fff16060ff1602fff0a87e7f1f811ff05c11ff16011ff01811ff0bc11ff04811df11c11ff0440aff08c01ff00801ff08cfeff0042fff00411ff08c09ff03409ff00409ff0bc09ff02411ff2e009bf19409ff06c097f0240aff00027ff0002bff000c2ff00024ff000efff00088ff00045ff0008bff00028ff00060ff00018bf00055ff00002ff000feff000b8bf00065ff0001b7f0000aff00000ff
  | 10,1,0=>0xbc27ff04427ff22027ff09c45ff22c27ff09c28ff004277f024277f0bc277f044277f220277f09c457f22c277f09c287f1f82fff0082fff16060ff1602fff0a87e7f1f811ff05c11ff16011ff01811ff0bc11ff0bc11ef0bc11eb04811df11c11ff0440aff08c01ff00801ff08cfeff0042fff00411ff08c09ff03409ff00409ff00409fd00409f90bc09ff02411ff2e009bf19409ff06c097f0240aff00027ff0002bff000c2ff00024ff000efff00088ff00045ff0008bff00028ff00060ff00018bf00055ff00002ff000feff000b8bf00065ff0001b7f0000aff00000ff
  | 10,1,1=>0x10827ff28027ff108277f108276f280277f280277d0a82bff5a411ff08c24ff55409ff08c27ff08c277f03427ff034277f1f827ff1f8277f01827ff018277f00427ff02427ff
  | 10,2,0=>0x108277f108276f280277f280277d08c277f034277f1f8277f018277f004277f024277f0bc277f044277f220277f09c457f22c277f09c287f0a87e7f0bc11ef0bc11eb04811df00409fd00409f92e009bf06c097f00027ff0002bff000c2ff00024ff000efff00088ff00045ff0008bff00028ff00060ff00018bf00055ff00002ff000feff000b8bf00065ff0001b7f0000aff00000ff
  | 10,3,0=>0x108276f280277d0bc11eb00409f900018bf000b8bf0001b7f00000ff
  | 11,0,0=>0x27ff0002fff00011ff00001ff00009ff
  | 11,1,0=>0x27ff000277f0002fff00011ff00001ff00009ff
  | 11,2,0=>0x27ff000277f0002fff00011ff00001ff00009ff
  | 11,3,0=>0x27ff000277f0002fff00011ff00001ff00009ff
  | 11,4,0=>0x277f
  | _,_,_=>0
def q3v : Nat->Nat->Nat->Nat
  | 8,0,0=>0x6c65045bc1b2e0652f0fc1b195bc1b1955d6f06c01195bc1b0bc656f06c65181be3a350d5bd7a4d4357741b350d57d7ac651833c1b050095f06cb8024fc1b194096f0a87e195bc2a1f8d47d06c120457c1b0500a5f0504f02b5c1b2e00a3f2e01402a7cb813c0ab72e00b02af81b1940a6f0506502b3cb81940aaf1a8140297c6a2e00a3f1a865029bc6a050095f1a8b8024fc1b57c096f06c990297cb82640a9f051b102b5cb86c40ab72646502b3c6a264095f265b10275c1b848093f2e0990267cb86c409b7051b10275c1b264095f06e10028fe100500a9f8404f02adcb81b40abe8406502abc6a840093f840990267e106c409b778db70275c1b840093f2e1e30267cb86dc09b7051b70275c1b78c095f1a8990297c996c40ad71aa10028fe102640a9f841b102ade101b40abe
  | 8,0,1=>0x396d27f6c4f19411e7050650473cb8050659f2e04f196dcb802c65be08c1b0517c0e35009dd1356d243cc0b19411ee2e065046bcb835009bd050d4027741219411cf06e050257c1b938093f06cd4025f41b8b0093f06c120257c1b0504f570d41b0517c0b19528ee1f81b0517cb819460af06ce10517c1b13cd3770fc1b0517c0e350d5dd06ce50517c0e3509fdd06c4f0bddc1b13c11770a81b0517c0b19460ee06dec0517c1b050e25f06c140057c1b0502f5f06c140457c1b2e0141f06cb813cdc1b2e00b3e0701b2e0fc4f194e7e71f81b2e0fc1419460cf06e2e2e0fc14194e2cf0fc1b2e0fc1e350d5bd06cf82e0fc4d35090f506c0b0bdf81b02c117e0a81b2e0fc4f19460e706e412e0fc4f194d3e706cb8004fc1b2e02f3f06cb8044fc1b050655f06cb8194fcd45b4d5f9
  | 8,0,2=>0x384d0475cb82b84fb72e04f34edcb813c01b72e04f0bedcb813c11b72e01413e5e6c0504fd70784d242ddf50504fd70504f6bf5c1e13401b70784d026dc1437c4fd70393b27f781e1342fb70784d046dc143484fd70504f38b5c142b84fd70504f34f5c1413c01d70504f0bf5c1413c11d7070232e0fc1e050099f0784f026dc0e13c09d79884d241de3c13490b77884d2435c4d6a090f61358d243d44d56c90e70842a078fc2a1f81e3f0484d0475c1c0a8b83f0a87e2e0fc1213c11d713c2f34fce6413cd3778604f34edde713cd3d713da934fd84f628d3f513d6234f9c2108c1e3f2e0140267cb813c09b70504f0275c351f8145f0a87e0517c2a1f80e5f0dc7e0397cb8048119f06c0e0257c1b078093f06c18024fc2306c656f3516d027e41413c65d708c1b2e0fc1e35009bd
  | 8,0,3=>0xf07e0497c2a1f8477d1a8120297c6a048115f8401202a7c6a840113f840120467c6a264115f840990467c126c40ad71a9b1045de106c411b7265b10475c126c411d78405102adc6a1b4117e2a8ac046dddf2b011d76c46d047d8122b011d708423060fc0b65809fc7d04f0275e4613c09b795c140267e732e0093f2e199026f41813c09b70484f0275e5e050095f8604f026dde713c09d7884140267c4f62809f59a8b8024fcb8048099f960b80527c4f02da0f60780e0067c1e038099f3e0b80527c4d4ec90f62e0e50527c1e0389f9f13c0b0bfd84f02c11f62e0e10527c4f02cd3f62e1ec0527cb8050e29f2e0140067cb80502f9f2e0140467e472e04fb70500b68778b83484fb70500b38b780e13401d70384d0275cf82e04fb70384d2435cb837c4fb70384d27f5c0e1342fd7
  | 8,0,4=>0x38ef1173c0e3bcf0db078ef3c2ec1b558096f06d550517c1b2e1553f06d55195bcef350f0f93bd7d3c3e40e13427d708c0e09f3c1e038279f0784d09edc1e4ec27be078d409ef40e35027dd134d409fd53b35027fc3516d09fe41b050275f0504f09f5c1b2e0273f2e01409e7cb813c27b72e00b09ef81b194276f0506509f3cb819427af038271173c0e03445cf0780d116bcd403445ed0a87e361f45336028f5060170a2f4580bc28ed14c170a3d4d214c28f514c580a3d41c0aa2c3f4fc2f34fcc2a06e2c3f0a87e66df42a1fa065f0a87e8b0fe5c048115f7b4120475c1276011d7880120467e0404811cf049970473c210a8183f0a87e060fc1214411d798c511c5de1714471b7774511c75c5169c71f61458a1c7d45156c71e70a87e0497c311f8125f060120467c3c1f8477d
  | 8,0,5=>0x1e0381f9f0784d07edc1e4ec1fbe078d407ef41e5b41fbb06c1418d7c1b2e0633f06c6518dbc2a1f89b5f9d87e26d7c2a1f9877d9d07e26d7e741f8d87d4cc170a1f4233f0886f82d56025bdf6034456f034f0117ac1455809cf2e156026bcb8554149f2e15513edd550504fd7
  | 8,1,0=>0x38d409d744d35027754ecd409df0d45b427791609109db40e09c454f0504f09d5c4f00427752e01409c7cb813c27372e00b09cf8b8004273d0506509d3cb8194272f004d1025e42f180276b14cd80a1d5eb0bc60cb0093d047a4120bc11cb1442f0478c180bc11ab1445815794581540ae91a82f045ae100bc11ab2642f0472db10bc11e32b02f0478c0217409e906001026e45815409e908c1e0387c230780e0f08c1e4ecf8b80504f9708c1e134dc230784d270502f0472c1e00409b91342f0478c4f004d3f12e001026e4230782f2f2e02f046ac230796d2f06c1413d5c1b13c017506c140057423038d44d06cb80507c1b2e04f3706cb802cf81b2e0013d08cd45b5b41b2e0652f06c01195b41b004656906c01025e41b0bc116b0046502ba46a004097984801026e61000409b9
  | 8,1,1=>0x2800d091b5550042779280060ade506160276d5d82f0472c230341f2f0040918de41e108272f108d409db418280273d0604209cbcb8108272f108f009dac42360286d8984209cbca014427752e0a009cf414280275d2804f09dd4a013427752806509db4a014c2775048a009d749b280275d168d80a1e49d280275d2c82f046ac070182b7a1bc060adcc7e060c23d0780d090bcd4034246d00556027a423078ef2f08cef351b4233bcf06b08c0e09d3c0e13427570780e09c7c1e13427370793b09cf81e350273d
  | 8,2,0=>0x8c1e0383c230784d2708c0e351341b0046569
  | 9,0,0=>0x48580477c1201811df7b0120477c1229411df0482f0477c3c1f8117f048470477c120440adf1a811029fe100440abf2641102b7db10440af71b41102bf82a1f8017f08c2a1f9fc1200411df0a87e025fc7e16009fd048090477c1c2e009bf0380d27f7c140bc09df050090477e2e2e009bf050e20277c232e009bf2e00d026fcf82e009bf1340d243dc0b0bc09fe02c09047f84f0bc09f713c09047de412e009bf13cd3027dcb800409bf2e02f026fcb802411bf2e0140267cb813c09b70504f0275c2306c097f06c0d025fc6502411ef050650277cb819409bf0fc1b025fc1b548097f1f81b025fc6518009ef06c01025fc1b0bc097f06c09045fc1b050095f06cb8024fc1b194097f06c65025bc1b0240a7f0500902b7cb80240abf1940902bbc6a0240a7f2640902b7e100240abf
  | 9,0,1=>0x49760477c1e0341fbf06c0918dfc2a1f82b7f0a86f0afde6e0a82b7f308170a3f56904811df08cfc091fd5555809ef3bc0d117bcb855409bf06d55025fc2303427ef0380d09f7c1e03427bf3500d09ff42a1f8277f0a80609fec0701827fe06c0909dfc1402427df2e00909efc6502427ef1602f09fbc7e16027fd0481109f7c2322027ef03427117bc8809c45ef1f8d809ff41709c28fd160270a3f4d809c28fd14c270a3ddeb16060df16065183bc2a1f81b7f3fc2a1f9fc7e16060fd9ac2a1f9fc580bc60ef0a87e0bdfc2a1f8587d0a87e045fc580bc11ef1f8120477c1805c11bf804120477c5101471f7
  | 9,1,0=>0xa8060aded690bc11eb08c0d091bd5500409f908c0d09dbc0e034275f0780d09cfcd4034277d0a80609dec07018277e0040909fe47e160277d0bc1109fac23220276f03427115bc7e360277d05c270a1f401024277d0040909de414024275f2e00909cfc65024276f1602f09dbc2f044277b0bc1109dbc2f044276b0481109d7c8809c456f160270a1f4d809c287d14c270a1dc580bc60eb0a87e161f4580bc11eb0a806045ec7e0bc11eb1f817045f4020bc11eb0bd3d047ac120bc11cf0482f0472c470bc11eb0bc1102bac010bc11eb08c01027e423034096f00801027e40117409f90042f027e40102411f90bc09047ac1400409dd2e001026f4b800409b92e0140267cb813c09b70504f0275c0119409f906c01025f41b004097906c140257c1b2e0093f06c65025bc010240af9
  | 9,1,1=>0x42280276f108a009df442280276d08c4209dbc42034276f1f8a009df45a018277b1082f09dbc42044276f1088809dbc4209c456f1080109dbc42024276f3bc4209dbc4209c246f1088b09dbc4209c286f2805809df45a044277b2800109df4a0024277d280d809df4a009c287d2802f09df4a0044277d308a009df45a09c2b7b2808809df4a009c457d2808b09df45a09c287b
  | 9,2,0=>0x108a009db40102427790bc1109dac120bc11cb2e001026e41b0040979
  | _,_,_=>0
def q3u : Nat->Nat->Nat
  | 8,0=>0xa87e1602f6d0a87e1602f692e01413c099706c1413c095706cb8050091f06cb813c093706cb802c093e06cb8194092f
  | 8,1=>0x1684228027691080102427692802f04427690500102427592e00102427390046502427690482f044274b0a87e1602f691f8170bc116908c0103409692e01400409992e04f00409b10504f00409d106c14004095906cb8004093906c011940969
  | _,_=>0
def s7 : Nat->Nat->Nat->Nat
  | 8,0,0=>0x37a08b15bc88e1a3ed3bd492da7c6f9001a026dd7196559271fd10eb27250275dc48d1a12d98965b4b2c3cb541e0d65b1ba3fdb2527b4e79589c4693a0c7817f5cf991ef17e422ddfff33fa27d4c2a21901d17115dd07cf82454a242269d193c4af670e820116700e859e5e4129b076924324c58b8dcc84900be7a2916d99fad2436d059697ee64a45da57de3be5dec3abde0b5dda3d977658cf672cf6169fd57f3ead3f84179f3b55e421766a1f2f1ecc714967509b6e264091f9d0dc2a461685b84ba9020dc417a7124979ea5e13214a5203ed2a143e8474586cb3b459129a
  | 8,0,1=>0x1ea6fc84bd41408fa5b10e2950972891c93a527fc2865781656d3955db19b024861db1f4d9a40dd1d1b854600f498520c49be4c745fd0b76b19c1d7f9c9ab0859bd4428692c2c8de349c49a6b279d8e7a2c877795840e1534618999d2708644635223264c958bcceb7bc4a4e8de564c8cdd33971fa585a1b26d93d666f77ec4a4ba3c023f8fc4e6f5be56e921247422ef0b97812636b9045d6387fcb0f19504de5604ee483a41245cfc1a1a09c9a69420ff93b9d4e9154d46f6b20d133ed182b1070c5971a47596f74d51630543b8b0950b5f984bf16249f288929a461a405a
  | 8,0,2=>0x644c000a26983f2831ed96c8c4b3345e3210dca4414ec1f456d29784575400008a4000843df5ba0457d3063e2f73cd515a203608b00aa33b5b9dd91815e8894010d3043541e93b45b390000fb15d1e9e502f40000da620f01298732dfcdf206c60512e3a79d2428eab000104e000244f3d08df9100901a0c45dbd77ee31109d4a216001601685282fa6d0aec51dcabea5054c99a64e3094856f120a03d96a64cec1412302144c955a79c291a2040013344a6966c938999a501b236417169e61b100008eb0ec5b1d443e9b14d4452100008631ff27098304b436d3a139744484f
  | 8,0,3=>0x864dbe18b21bb722b621138d16d423a61bf96e65ca29ce2d903089d60002079331464053058b952bc00000029399195113092856a005400022ac623967cb6301cc23915680007fc5c723c28ee00b260b19232287a0240008d7d2fd39a60f50000000039445c4715d51016c4fc6e05f8168a09b168fcb45a6f668f3b854ec2dbd3d9600dc59413ce772e4682190f01c4085220777329b2877c18400001199765ad91d240b3000055c54bdc1021adaa90224000a3e272087a4d9786050750002135000000061259a27a220846dc4f016b3891966d82117584851010d6af6d64937
  | 8,0,4=>0x1b0da3d1c716f569c1086698114bdd491aed5633ac8d91917dc0100015e003480006bc648936966611c4a05901344761be81c71845d2985354379b046500002497427e6b15d062c46b46909a0a4e3fa19e0557c3dcb778e52ae07645ba53e5a2496d95d9778253b3205929a1fe8b98d290ae07440e90ad5a0139363393faa98791d4061343078b9a04281a78422b5e2664226b21298e45ba623cd570738537960e58c925dc00000000a92b7e7ac715549184643a558e451d1cec0000925bfb6b6d0f70171b2e3d30eeb2f822f982180000001b9a5e1df6100000760fadaaa
  | 8,0,5=>0x4c1980b51e49dc04464840625f21505a2598d6c4014774d3214653e517480517f846aa2080d1e028536723e45e002098c36afc6257f0c00072fe439348c00044b0ea73eea6016544000a20250040e5f3551c55390b059371c5a6a98704e714b9654b6475af967f06615784b71876400064658143bc9fb527286cb090402d4ea50018cc58610001df1384dc0a7330000000126d57e624359bd9b962dc3f98bc4d7958c48fb29813703ccd0bf19ad2098fb53ed6725eb8a064287809d5c97748011945454c4ea210900b04071f040005b25a6ca1ddae92d95f8f857e87909a4000
  | 8,0,6=>0x975479813108377a8a0217de40006cd9aef5a297b985fc000911d9593bdc5f15edda84829c07906bc12100602892c784784c9e47c5ae4490a2a58414f361c920fe4c1866d4d9a4c510547d22a51e25cb100000008f7179f608476f5c852c52844b6915840002f7296a8e129f44af5df45e9c2daa14c0f3555e3636771753557c9f90a653c13b187ee8505c7c260c0000001bad48c96b196e0aa3828cd816d50a015d84ee99094ea558b19096cfc92d8444f21230c5540bc4f7704549aa2cd02a1a404dc18d580006fd4000812d5a99c8425f1069a497d456d17fa4b2a7069541
  | 8,0,7=>0x80fe4190aad3b979087ae17a53ae560c83da07c131048a57b038a8af1e51c45244a2cb2a058570f103290000b32713d90d0001ee9000154988bce7f271472978d8f1200000ef74b40490040000575caf89ebc00088528d76d440003e9cd95000258ba670ab800ac1ce6f04000098590325327312a34a9d1688b8c8024cd91e4662e67ce1b3696dde15b2daa42e056cf6ea902103d5cd52175db40e65b2a9928000a57d0370001f29308dcdf00014b1571e3a1648414501f867a22a63cb0000000216c080768d99b30786d99005a7333e655b095d2e92d64231311c000577da20
  | 8,0,8=>0x64cda10262d8ec07c66649440dbea344ef104a40343c307ac637949f8644f03170c6341b948395b5e7e7044e33f954614576309975070c4b53c634118e03417cf57bb88dc0006c0a7b9a6640008344ca92838d89a1e0b7b7884ba76e944e836fe1799268a131bd8b7c6605ab40cedf5762769722c464825efde4c2c7d0480cc593103453d5048e231932d16b6d1db0619b50cc946915624b846880a60f77f044557f152111cce174a02144278646996ee64b15946081631c212908e14f2705c3d0d0c8b39ba5cb916c63a993857ec2b3c17b21d4ebba21068c93f25790088a27
  | 8,0,9=>0x6784be9030549997c4199a70d2236d3c20886a53917f646c302108110070d590351bcd2c249d441ee92773686ed6d9db913a243c3a104ce873398a38ca4c89158d4a956c5331a004aaa28a61833df63e61ad5d672a89abd62961572214af401b62df026630801de36098846b96f81a717965a295bae4331b05a112ce62d173a450991464691fc60cb9bc45ff0f057da273a52a90a64a98d506911015f7f20ac7b47e9c87d54c68ab8b3e35846dc0090bac79201c47f9a735bf88c2e4ba32f0351127e7547e65d9b7739b996d70f69652d6a7326e00305a585f5b8da9638243b9
  | 8,0,10=>0x71fe86a00000009d760f3110400000005cd65c52cd946539a00014b91078e212d2dad32bc896f3415e92000197b3bda3f9a250344085545700028690001c76a4c030925cd451299a46733c03918a268d9280d7c20ac669196ec0698f45b129d0436b4bbe5693becea93560000691c09c91bc01971955c161443e1244000037540d336d60c934440a320057c160c60d700022c00001bb83a8164183e513ba6fc0425910d935de55118665469a58655920ec0319de249032d87d41a5d1f167049cd23c5c5d6d6dd3387d661780e4d7c77a67ea46346b17f7d0ad31ce0f1a5e46e9
  | 8,0,11=>0x27cd0cf6a2649547656179445f873ad271aa3b04aaa4860418dc5c289219e7800004d0645e9a19ae5c8431903495fa84371eb4a511c698ab222caa1686dd31333a92f67ea50aa644ea336701080000c2f48f1222042680710247fb5a38e99a40e249316a9f11ffd81b00c87089ce593430e44045ff285740346a1658a3b19fbc7091f5cff15384eda90c475127323045d5a80c000005e14e5c2219624b987f62e165e5a59774e23b6165f6977e9dc60a700a22d1c429a78dcf759a56a149089ba512658168327191e5c000553d691078a27931a697730c40001065a8b006d9d4
  | 8,0,12=>0x91253fa0149547228685964adca550a4fd75284aea54fe6e14304091623e8638f25149650c3f12645893040529110515a15afca6e00bd75a3e4886100001df52244db77927139a868122e5a7e16861ab155c55e9a6e40c91f38c550c843e98d656619ea047214c5c856a307f62dcc951368592591f8f5633d22290000af08f3c15f382cebca0edfad2fecbbe66b00440001459212e96738ba6f871adcfb58697390e842e08064000569e0cf2ed87711b14af9a288000201c000a03d1c77d2d70190b4a441c0005f8ee408150cd99399f1e018ac471ca27a7f107d800010e4000
  | 8,0,13=>0x9270fe46e4878d04a876c99500007b30000a2444615d9880b2ac84c036c40007a2c40627bc38769a071e97b68e127004d582d497c6d4ce1c6bd153757ee923003da2e120632b6fc289f58908e37d9e7494c7c7d109f083a6a349b3a14496115289b90825c4987ae8f38565af51a9def929da29d9d6c0003a7677f2d25131219e1e1229c7e194959a665715af75a44af89fc00069f4630000193b3b0cef33cf95e40784f298da4a9521a697b92464e912761f1215dc996955dc40de54979d91f892ee578f27a664082216d8986cf25841045048651f9635c8df25a52d536204e9
  | 8,0,14=>0x1deda62a231e2e139dc6a2ffc10c287e4be961e86107d1d5b56e421f21cd48f228d60972a49fb48a9eba46619b428edf11564620900011e17dc400001c84c20d8c0f90c640411e8603732984993e38ad40001b793a5475f7d0cec429f815e070657359de28f107514e4bc47e474a0426a6edfbb337902d8525788198010a519c9144d061bd72065ff266c9719f64fee9184dfb96a40398aa484d08dc59221bcc11650650242bc0ff529c000154a7d154a4ab09d4506119cc0007f250e68a467005484a646821f018334fc7448653200a54818a068c900025a2982483c827c1a9
  | 8,0,15=>0x8f69498c3d5773e3e25b10f659711e5acd0000fbe2f0e7908e64c517aa58470030ca45e465e34a2e1c3712860153fe26973c4d4741f930e2740000508c5e5574563ca4a5c1288e65a48ba596f653d06b6591687152093f21960d305d433d5964daf69ee24b1eec7798a840000291bc52a640005aa4000000282b4f2624100024a27e44e876f30bc096ac4a77c25a3774043c970119926e8528132fd25d8e247627ea40c436c81f77fbccef494e0171f651e959fe6d179a400046e51740800e4676aa4534ec57291ab8240323e0ff816e9aa12440001fa67c503f5e54416e911
  | 8,0,16=>0x8744f9f0000e5b9ca60673f24bc9000199178f28a11c8d9837491c359c04c9929d09398a65db901fc000541d73327ae1b980c52ac4fca0891524ac18c697097b080215d919042b25bbd68aa636a0e4ecf4d7d71d3c55d530faa14b968695887ee5206fc4da4958d280a5ce96b248c6f85a64f1967b022c301c6d52785a09255c90245b810b2d50a877f44a378314e1e40b938170a423c3e592781d9925194e464c0e248b96810f3f037dee44665f77537ce6d5000a7935a4e818f54dcf0164c95757d1a206542e7160a1217e85f3387e5ae30881009a5810548f90a7c8265319
  | 8,0,17=>0x89cce750a89827a05e2fc40505a9224d59f00010859d695513a68f5c78c5b6f12b8cb84ed48f4518616115c87ef18b03077c646071cc68e9301298f55a5ce5a08c06358d0d724e4a9a967c5c316a515f126d65995b05bd19e6c1411efdd0a6fe8a3f3b8ccd2916400000000b73c453028b7502f93d4d4b33a9ba224b20d99708e0748063e5a47c14979919992a248061e8cb5f4dc52dd94fce6b741ded40000000448056c5ec42246fa5cf55d641629e1c9083dbcbf96a6c8416a0626164b1349687079c74fd3018f340008284d3a1ce4ddd4045409088e54107e156f8806255
  | 8,0,18=>0x30357cf1b36765003a8db31f4b9f46da9925dba83161fd71c6b84ad8396262386ae509064d4b791e9517a725c973f846e19375797a73c799081cea14c44bba4744f1d2ae414d52fe7e91f9a6f971d69d315e9881000151fa3e4342205e011748a7c984c407d403e571419dd0e7e8e0690dc57a928c69895a242321fdc20a9fe49de00017f485e013b4f15c1876040aa4c85eda46a58094fa6471092d14c3f647a2756558f479dc8f0a8e4fa5b7c6c9420d7a17346169151e0b924a4adc359c47174e6077845c88970b4ec18c24b011fb60e12a141bd6cc424c11de29b6936847
  | 8,0,19=>0xa114bb83ae20d52624eb6a7642dc714514633129ae26a676f626e9a64ca59358fb02a90f45b7a63e83a993b6477a1240b92bfe899055c8ec941000d6284ae175e54c7a7a67a4091d81708128714e76619936558707182f92fe09f10da81a619060a96a8843a00cc95907ce70a7c7d5012fc9a23183cff722654e789add2b17e4e67736e2c9886c61d4ada2b92cc04f1461829a2090e739b2671b2205ff988a0f813ab42b93806797235d27660b5e12a2c58f72505cc293544b08184bd11a0558964e4b41539a7b34244de95d2556c133c871a4644b88b4d3e1247e804593a4cd
  | 8,0,20=>0x3b64a6357a2591a0ce7ff21e58d25665a5193468c440383e2594e54574663e267aa2b781c665c5609a8f6585d418f04f66a37d9942c5d5dc1ee42d17e7c012869602f3d1da8382f49f450fd4081f251aa0dcc2212fd0a396f265894d656f444658016fb524720713af339e4cf2410fc1
  | 8,1,0=>0x9546894dc681023ad972543900051c58b6b46a253307ea610cba030009528b992e2096a46d13e90b53928ef4679ef6419bf81f045721a4f2992b948fac10614e783934a85f1eb3a497a8f14cf3c99798c14890918c32934d72c905b6c19a75c954f0006699690d354900041d2474274e1804a410009890ab0923a1048a2f3910b952b5fd6b97fd1f50d928a5aa1108df7d00002dd7ec0124e99495b70003215f149b9998898ab9d00426237f29019399747c99590597f930d5594a92964a3779
  | 8,1,1=>0x9c1739a7700a36147fa8100096079000098d0003fd7038c902f52d2139b95b91289211b94495240009d84e8389819a58696129a799dc1ef20d3f1a7f6d96aa9f90009099f0829441acb4de3ae352a5c8d1445a996386301b194b73171136900caa9461663723a6345903f289a2b4128b38fc4f79914711cc4bf8516016e17299719149f532295e6e94438318412336f197727c50c20320b031ad1ab469929c4e4a5aa697d411d82c9436b61fd00060d4b79818d95712a2a50a0f371812253
  | 8,1,2=>0x39c33e8bc7e0a596a9a0999586196c0db8499d932e19991c27907fa237b99616ec9cc0f14fa3822bb9479a11a140608264943b3e36435318d39084934d18cd751a3100b3d476455791921fa217da2ef7739314c76186395d175f8794a12740552f164d0a76224fe9d100055261f0006cb65175d7b01f13eda520ef8813b60241d4871a0b5205c148151400095a22105d05375b6dc95c6f97419731bf0131644b154374944d3af0001377e18f90000a11842a139a0d528da0d4d94773488fa65e
  | 8,1,3=>0x1e1011581823a4977127658c5e924ba1179d9c7a4d19f22999f6e2a835f996b3d93793161c32619ff24f66f9340217018e92397102a97d157c9329cf16c0001898f62e692aa2d69186779f6d3a13561acf1d009b1e90000000000003b9ac986a92f9107ff3816714c16799639b07532ac7595d97835f07f625f7c17a142971f6f41af2596774d340f0ad33570989138a6c978c6a10f97b124936801b71935f70dab901906b13d14408988726e79190705f62c876a7b00f7bc3090931a983477f
  | 8,1,4=>0xa914975842317dc45f2c378a7810779e14510008cf7ea04f50a6ca69e25ba0114937b90f1d842d6bc8666f72b47f4000a3c77d00062768226c9d75357de694001000000632821a64a292d11514990141013c45e15b197521991128300054768c5a1227159ae16b1a3989f04131b8af7ac46f8b7814201a19655504450abb02b14d8993074f117c26500da897fb1f92411175995881db062ac78e029e2f94ef8a149179932f8b152765c0e464f9240351e73e6a512949b15900c58699f36611c5
  | 8,1,5=>0x941a201710001943703199c82814b90f54329e469a5060498e180a000aa1929000a715916195690da7d993a8a976900953bab1
  | 8,2,0=>0x247118a0000a81690
  | 9,0,0=>0x686077ce767d93cabf5d9c23f9714be5e1a6ad748b8e05fd4cd96193f7db4ae574b78f8c000e3a433c30427e0000000f0df329ef06880a5e6290c000351d6a285102fa8e617723f728903520a26b8bd2345ab27720488000b22ffb2a2afdca0459028b88a63f88315ce42461c304f738c645a43019712462d4d60e97f89dc544f02529fb4f93e44380c19dd816a95079cafb4cda2e1171c77cbd21fa5c980021a32211ccaea5bb2f798384a451f2eb202201c21f2c9514640c5b7e429598a0065926669040c0c96e0c30b49be4353198
  | 9,0,1=>0x46b8dc529895b2a1cac974e10164dc764512b4b7dac7a5102f8958da11dbef06a300c925fb2f01611a106372f91518800134e9b9540bf44c5275100013e6426f4789cb10cd026ab2413104df81c11b48d5ce6e110444931015a52d20c99ca4d6bf9234c549aa83bf1f4902648627f5290e859622491c90d1d4c87061e3800000109a2d500c8e4465f25e324ccfd1466b89ec64b4c8b78425dca1308128582663349215678001c289fc115866e2e2e30941b5c8d1cc2b6d0a73e544ae151b897ccc2afe23cc086301207200a624252493
  | 9,0,2=>0x811b609552bd4734a5c59026311b989e192ebc95178e6d38266c3639cd0d42de21420945ce65197f645b0dd485922c3178b183d15d6b0297325957072ee58f65144538b3c672fc15ed23de19529a2acb58a0deb4965525856d8e110a3b30cb171476bc95bd9128df2721664682f2260494eceb4af85ac80005168a914eae1dbb430d1dc9511fe69792be0ea8a691d764e058470622c205b8b04fce590abc60625814967d9ac462b0b34a08000aaf27544ba6c54fef6f1111da519ea79563b12e402ad992a3ef51b270406480e9b8519f
  | 9,0,3=>0x7f0b3895644b17b5c1cc8bc8197b89bd4da83916a317697fe8e189095a60e325f185c9851fec94005c185ba031c7f4b4a8ef205e514b18d7d2e5b1648644d22c5a5feaeda3e21411ef9499a3e3291e49ba5933045600b171822def07cc87c98a7a74f880c05562378be3ba44ea837710c5306c20f143dc988a8242d028b04d996669945adc55d2abf679a8840b8fb31c59a7c0d43930b7ae045d26e1668a17d9826a694d8000b58000580c624c928578fcb629ca6189730a7e9ed307530cc7864e23c143987c4b0abcc090b771a0910c
  | 9,0,4=>0x8a4801dc8217425dc3a6022000629abe8000f2438cb805b12f492df3ce06ceebc51fc82e3280000d8b2843432292b0a1ea2c246338982ae253131188a43c868d5195c9e440009578d8b34cb42bc171909c5e829310e130a50e27052a8a7d20a29193cc0ec5252edc5613e4ddb05113eb45a542273c3010b2df72b2f684ac24e2045371b23a41731192949d04b0c999927cadd3222d92289931d98d3269207a4fe238c434c1ed762db19398d7ddf12574f0b2a47ae9a117b80686f46bf7140951be30390dc809c2dcde12c0b9ac892107
  | 9,0,5=>0x11511686a2000674bbf00005e27949e159b62140004811e9e13167a2a44440d8c74dad85f1f2818c281c40000597d091c41125d1271c5d45364ea304b6640008c71c4b871b3ad841408000d5a58a928afd081e9f96b48001e132238a8ac45722a693b095c4db2b7275481e87e29e7120ae318d312421e09584726772de30e84eedd56012c852252596a51e5813419368c3c68f3206974499d817b1c72d4b64439e1397cfa0e604f0492dc8d25a021ab6ca97e8a924da5f7bc5ddc245c7a88f661124e1210a6049e223168a8a5e002457
  | 9,0,6=>0x71f25a4e38679335b45856303d4d480024720002c6af5d7129b78369ee50de127180c60d8368611c509da39e5162242f862b2bc85cf878501266a5e84664f8c00057892a55feaa10004590f2edb7918800000127c1ac9ca89425ab4881f3de2af190368001432000457c68553228300038dc3a02d10de0be620220391c3c61c7200083741b067e20a86cb6482320007d4a9585e313c8301dbd93e081010accc00051b7f5b5855f23096988e8d4be499804b27535e0006388d0cd5215900000013d270d11f836e19600067889e4d6c899
  | 9,0,7=>0x4e48755ec307733203482f71c9500b368e92a591908a857887f93b295ee2088c973c89857be9d1664c4d12a218b00034520ae00059dc1ad12200000015e98c0b415fe422d5ce37e34397c5b7282f384194400000035f1be0368dcf2bb42c8af2e44908976527284f7e4a82484a2917908000a42b79269bf6e4811c10bc49e814c27c26d9fa64980018169885b530ac22b391e26a7e2177c3106f9250725bb110f26e220aa04658870f2a6af1c1832777c0a2c54e2f67749ab0138e2578bfa305972bcf4889470e840e626c972531e755
  | 9,0,8=>0x47894b0572c5190cafc5892c796f4b0859644550bc957c00047b30a2085e5600d43914f0c8e7da6418e1e15253118b8d3da407b755981259f22c76fc800151e394000387dc7e7e159bc3c62de60a85080010ef24169f80aa512dc104a2574996d9a5209180b98ab1160ca85f4f26913db065f76d1d5f996259224b9630b6409d25c10bba81d5790935578604d92d5c5b4915050473122936f4a6efbf49fc5ed093109239c6a4b6267f61c9e24b28a730ccb93c346bd1913af6402202d59c8455fce3317524744000f0b58c98f02d5069
  | 9,0,9=>0x6b5383d6532b15fa81840000000b89c499f8b434a3b926222c6b0209a9d6f672922036049ace5570ccaa4a989d9796398e2f08b9726c2e646ae8355cb8258e6cea6f289a54931797acc59de40ba19048c4e22865e0001d910fe7c10003eac4b80003d741057f6259244932505322b
  | 9,1,0=>0x7048287384db307b4bbc35598493580f4d18698393c12d517249c1419a4403a193bb4c96995874629a739b617bc92cb021625539ba9a5769a7da79b831a049dd7fd5c92af4ef66b44902a6ca94990783406db3197268832f8ef32bb99a913578993417925a17a32e1b717ef761529bc87c19191795ff2b9ac181730385c81c314ad99f998131125493d63fb2768f6f16416b70e6619779749ab1721044771bc45d100045195c4b10008948795419cc96a86649d35d92d429ae4032784071000
  | 9,1,1=>0xac90001a11c96e4b2fa3905cb69aa90015978d174840d99139e1714a5b01041789b3fbbbb39b2c2897289c40003ca5273390006f785737c1830001d858a0002139a1b8f3f900014f39f83bab90692597bc3a60001910004597e13917394673887cb0b581953145d90ba9995b27bbc19dbba1b4b000000a5f73ab3727d8a19b95518c3a1c62ca416d125f2d36912e94df8f72dc4d566404934c55f03a0bd6d39133a058b07a959b8d0f1b51051a712a960fb552387d22398b87946eb409b610d2
  | 9,1,2=>0x2995f17b36879997d969f7410004f99ef8ada7f0e91805e49290009c54d94e16f47980006b900072fa8918b3134cb649ad50001b39d1000ae19051014a85095d30d18ba11d7094aa82e8af7a1b0973072439d5cf7527b136136910f301a43a74a313e95f97f18d05bb84b62f76748d2b17270118417371ab5c10f92c3b341a36113fb4b4249b578c4ad192b4ba0ab37549e4908b067a000979202466b19824177867811ade0941896a173f25395159f6514f760176912f2b78dbaef7ea6e95b1
  | 9,1,3=>0x1d7871b214a793902d3db4818d36718b1aa763940c24a7cca4d1517e9aaf8510ad1614018f9b4d56960769819b12166918130f55926947734e7817518b28cc1e7b9182965903031264a5992670c34ab47a3993a47c9af7a59061602aa02093c34243849699acb292c908905e7960009556f96b35898c1921000b4fb97b8124bb796c35e931b0007b9329aaa5d77316b18431189634945217349f71b9bcb3a2b472d74f1a618c969e9ba6849e902980a9d51a90db8fb000193000a49007a09579
  | 9,1,4=>0x9e15476e172c74c000aa499c5b9701a987aaa3f000a111298e924c9f139ab9f000261a800006a96c18140a68626ff40486b88c9719b22774310c1a971317164413e13d14c29890b9681a909096d906a511b5952f56f67b8e109121c47645c630199a819313192d1805a296fc74f9d92526c914741c70d00b1b12f978376517caf4631a9f76ba3ba3717f49186098c321a4fb3e3518f13094c18d97f9a2b809a2384900d4176bb8f3a79059439561bb91f19cf3f71c19d8a018553ab05f2919c1
  | 9,1,5=>0x45482133151f2cdab22420002a19b1a2177a2815a9af12ff099000a9caff0009a98287c21bc22c0c979968abb1a6993b5d9000390a83571719b933b950f4d3411307ae97474a071194d6af74401a1f9479b41a0c8b929b7fa50102738072954939caec4cd61f0007f5aa1b49b112511ca901000581139679a8d3a8b381c4000961b5364c0817732c109a81fac22979c9353371b891e941975727178b469adf92f8bc85946f22210988115f3fcb482f13f13b11765e136da517a97599416a3bc7
  | 9,1,6=>0x603169327a7c1dd14929f000
  | 9,2,0=>0x510c4b77d2e6531161a106ae19cb5c00c99a3a212d38cc6d0d027480576c11d9a5167b51a8436f192d0493310037d620b38a94f2296e484460757991df239391432f208b9276f73f8e5747780b9e2ad968802866330951f2ec4c96614cf068012200
  | 10,0,0=>0x185b51c9196e19726cc15500068d3157c00590423e4006240002c006fc8d39df9368093945f38c34730b515d21000000a9a9705b74b169094271e8f47e137315342e5815e40030ca12dc2c209b167c1b0f801405ca425e1670a33104f2fd71045775fd4a4d8e9509ab3c941724ef665b92ac3f584d11454b57911000003ed91264e400114711ed1a4006eca904d51064ed000b36e994745f12f53931da12f1c2
  | 10,0,1=>0xc93b0b13ac9108ce10cc003644e768210c50c4a4592ec0c
  | 10,1,0=>0x2e67f485a1a2691744917d189085f172cf4506196e4593f6718a8b59e23c8c6179e53c94632565628bcd91c96a82dd9861a9209e91864c1a4f30fd615592432584a65f73ed7f55d74096236453975ce9a0000928c134400a62219f0c3424f987e41144137847a000b70c400410bc8063a0a82c70e2215ca189d02545116d1b1605298a6817e43e9b41113e2b2a6490265a001bf5f954384005ae2028d3131e34
  | 10,1,1=>0x994645f0319f3a8009128b26cfc3fd0b6dc272c5c134dff8e5c965e09525fc0000002c33856113c4193d4b32ed995c41b0d0233148d108c480d4c6f0bf875df138f72f51c006422ae61
  | 10,2,0=>0x9b210fc4b07164c426590048d620c003e5a4012b802927a39084008d88bfc9f488ea44c2d359b9c4e8218c6664007e47e88a5a3d46133404845723e004a9b322270d05423903c552335097e08cc4c8024e006080192a789c06a60b001440139004b2430b34ca436e174d05be19a000000a3
  | 10,3,0=>0x44b89702ca80524cd3172000a1
  | 11,0,0=>0x74005949826181590a6828808d1
  | 11,1,0=>0x91a66b898482b2145d0208ea54a241a40
  | 11,2,0=>0x91a66b898482b2145d0208ea54a241a40
  | 11,3,0=>0x91a66b898482b2145d0208ea54a241a40
  | 11,4,0=>0x320410
  | _,_,_=>0
def s6 : Nat->Nat->Nat->Nat
  | 8,0,0=>0xb43f015e6064040144d0343a0201d0d8240200008800000a500805110010180c0642a080021bc020885a0141802c1200428028ad010191303804842020150000f024010082a064430dc17150220202a05c1c204000e80803000004030284a008031800400882194310180d0200000c34110093b0000ec000080800012074470100c004c1008930243c03002000000000d0000401c030442101c080001d00802
  | 8,0,1=>0x43b244030b42a0040101cbe0284500417000030705869880000001581a0082a08c00004236ac540dc2f034620581c0006515401000040444304c0400004018841b81e0443902412190070044e0580e000c7354150186b06806038a50000400c1d08c0f018010e8000040415800168050c801038000641500c0810006058451e00122801000000481500c000547000029000000000200c480001d1dc0008c04
  | 8,0,2=>0x4522ac05371610000b084162a8120443f000111292f2441a0c00307d280800605c00008b106c0c0140721615004010180a04c1c3840c278be358000300e02c012cc0817c010041a0f00911c4f0102205c4c014001500b0a0000fc06018cb0883e0087c1540500003044680b44800c3e06424058022fdb34711601cdc074210740e4dc130080f004010082a0d0061700604c2b0080105003000100200601002
  | 8,0,3=>0x3ad61084010d80b0103a030002d0063c00d00c0004402128031984d61114018090000607e250254b0981c1440004c0f004050586a014000301a34c1b0ec0a000a21581b02c01400698b0071f99406c030483136c1503493518020681017006000140480000001318010a88e7280a0341a1c90d010910d0bf124000e4020d8890d815008680841d0040201c5a5ac2d03424054aa29078134204540e0cc0005928
  | 8,0,4=>0xda094095502b0282a83088104010006836c0d1ee43390071f40b0e9760040803dfd05515010a96340c46414080bd088a50bc1d2a80401c25005f50049e1f0543e08a0440100002284610000c01c31030000047406816600021440102c77368000a0416702d06d0f0001609959010a3008a70005a31000278010599b064b626802208070000900044669b101401
  | 8,1,0=>0x1305a27c543001002c70455860585502c020380800084028001647200c0505c1211c0a038030ac060000a37c040042e4540200001001a209404000020540c04c1001c770547d0dca80cc14260020902f000020a8050741203410000000e8610001805802000180b000390000844d1800104c0934c091500003438018350002000000000000006b004020381c0201a01c0113c191480101c240440d008031d428
  | 8,1,1=>0x1d3440109c2a018060d4aa2188104425024080a81c01211568ea0700b01c231bc722e0b2030f105417
  | 8,2,0=>0x2a0
  | 9,0,0=>0x6000158ea0020004b8240080900006012e1b41382500a000898840400640082a04a0c81209e0000040a03f0083ec2d009012014000240ba1600183b0bc00402006030008020000900000001001a0300d014006000450040620480e8510000c80005600a0341d82400201c210511820681102c01a004000030060000400c0600e00080102e00c000000082400b0030080180102a0000000d021078010050160040f40300700a048060a201a0080281e
  | 9,0,1=>0x144bc1102e00006c7f0000b402c000040220000900c07000403801010080048110b40140303d0000a4e48000c605c4e8840020680900105e0e00089a0001981c00419e0080a80005e008010a501e0e8e58010d0014d00210000240000f2c82ac9005c002054000973cc21c018300182ac7c80400c0289f83703a0282a8290162681400601a1400280c03804c000640025f0078070260b00c049024004330000201040082d01247c1c00d01200005003
  | 9,0,2=>0xf8073290102681902f28a1f00c00a15e0100082f06014c0703b0020a4520102373005b8012e61dc498b40000a0cb825
  | 9,1,0=>0x28c0a27890020190940c03c0d0008501c362000f00928000ac27c581bc0102c110ac23008001145a000170440c018050040101410164a007c8203416224c81180d02483000000fc2800c050000000875020011bc2c01805000010780a0186e07c000c81e07001044000a44b02000038090cc1a1a8040788212c991a0170000034c0e02823004002100004004044030ec22004230e00001800000010ac0e03414
  | 9,1,1=>0xe2585a0d831208000347a060cb13c0067c052d4311d8210bc12084a0240000001c3596687c0005c340200d94c300080c0000a0344a10ca702402000041c4000200c09ddf05c0e
  | 9,2,0=>0x16502c19604827001e589800894c043a2df1f
  | 10,0,0=>0x58a70d85da24738464c249120001902387a04804d85063cc0a0034408
  | 10,1,0=>0x105ca970402a002eb869d13088088fa20529eb42041904181830ca11e70408007180c4810a31dd4
  | 10,2,0=>0xe410310a49814070431800340400101c6
  | 10,3,0=>0x1c1
  | 11,0,0=>0xf0cd
  | 11,1,0=>0xf4d220
  | 11,2,0=>0xf4d220
  | 11,3,0=>0xf4d220
  | _,_,_=>0
def zg (k t : Nat) (w : List q0) : Nat :=
  match k,t with
  | 8,0 =>
    let h:=uf 65565 w
    let bkt:=h % 625
    let d:=(s6 8 0 (bkt>>>7)>>>(10*(bkt&&&127)))&&&1023
    let slot:=((h*1) % 1048573+d) % 2624
    (s7 8 0 (slot>>>7)>>>(14*(slot&&&127)))&&&16383
  | 8,1 =>
    let h:=uf 65543 w
    let bkt:=h % 161
    let d:=(s6 8 1 (bkt>>>7)>>>(10*(bkt&&&127)))&&&1023
    let slot:=((h*17) % 1048573+d) % 674
    (s7 8 1 (slot>>>7)>>>(12*(slot&&&127)))&&&4095
  | 8,2 =>
    let h:=uf 65537 w
    let bkt:=h % 3
    let d:=(s6 8 2 0>>>(4*bkt))&&&15
    let slot:=((h*1) % 1048573+d) % 11
    (s7 8 2 0>>>(6*slot))&&&63
  | 9,0 =>
    let h:=uf 65540 w
    let bkt:=h % 291
    let d:=(s6 9 0 (bkt>>>7)>>>(11*(bkt&&&127)))&&&2047
    let slot:=((h*31) % 1048573+d) % 1220
    (s7 9 0 (slot>>>7)>>>(13*(slot&&&127)))&&&8191
  | 9,1 =>
    let h:=uf 65545 w
    let bkt:=h % 185
    let d:=(s6 9 1 (bkt>>>7)>>>(10*(bkt&&&127)))&&&1023
    let slot:=((h*17) % 1048573+d) % 776
    (s7 9 1 (slot>>>7)>>>(12*(slot&&&127)))&&&4095
  | 9,2 =>
    let h:=uf 65539 w
    let bkt:=h % 21
    let d:=(s6 9 2 0>>>(7*bkt))&&&127
    let slot:=((h*31) % 1048573+d) % 87
    (s7 9 2 0>>>(9*slot))&&&511
  | 10,0 =>
    let h:=uf 65537 w
    let bkt:=h % 34
    let d:=(s6 10 0 0>>>(7*bkt))&&&127
    let slot:=((h*31) % 1048573+d) % 147
    (s7 10 0 (slot>>>7)>>>(10*(slot&&&127)))&&&1023
  | 10,1 =>
    let h:=uf 65546 w
    let bkt:=h % 45
    let d:=(s6 10 1 0>>>(7*bkt))&&&127
    let slot:=((h*1000) % 1048573+d) % 187
    (s7 10 1 (slot>>>7)>>>(10*(slot&&&127)))&&&1023
  | 10,2 =>
    let h:=uf 65538 w
    let bkt:=h % 22
    let d:=(s6 10 2 0>>>(6*bkt))&&&63
    let slot:=((h*1001) % 1048573+d) % 101
    (s7 10 2 0>>>(9*slot))&&&511
  | 10,3 =>
    let h:=uf 65537 w
    let bkt:=h % 4
    let d:=(s6 10 3 0>>>(3*bkt))&&&7
    let slot:=((h*31) % 1048573+d) % 15
    (s7 10 3 0>>>(7*slot))&&&127
  | 11,0 =>
    let h:=uf 65540 w
    let bkt:=h % 4
    let d:=(s6 11 0 0>>>(4*bkt))&&&15
    let slot:=((h*17) % 1048573+d) % 18
    (s7 11 0 0>>>(6*slot))&&&63
  | 11,1 =>
    let h:=uf 65538 w
    let bkt:=h % 5
    let d:=(s6 11 1 0>>>(5*bkt))&&&31
    let slot:=((h*1001) % 1048573+d) % 22
    (s7 11 1 0>>>(6*slot))&&&63
  | 11,2 =>
    let h:=uf 65538 w
    let bkt:=h % 5
    let d:=(s6 11 2 0>>>(5*bkt))&&&31
    let slot:=((h*1001) % 1048573+d) % 22
    (s7 11 2 0>>>(6*slot))&&&63
  | 11,3 =>
    let h:=uf 65538 w
    let bkt:=h % 5
    let d:=(s6 11 3 0>>>(5*bkt))&&&31
    let slot:=((h*1001) % 1048573+d) % 22
    (s7 11 3 0>>>(6*slot))&&&63
  | 11,4 =>
    let h:=uf 65538 w
    let bkt:=h % 1
    let d:=(s6 11 4 0>>>(1*bkt))&&&1
    let slot:=((h*17) % 1048573+d) % 6
    (s7 11 4 0>>>(4*slot))&&&15
  | _,_=>0
lemma ym : ∀ (g j : Fin 8),
    (q6 g.val>>>(4*j.val))&&&7=vo (uu g) j.val:= by decide +kernel
lemma q03 (j : Nat) (hj : j<8) :
    (q6 0>>>(4*j))&&&7=j:= by
  simpa [uu,vo] using ym 0 ⟨j,hj⟩
lemma xr (g : Fin 8) (j : Nat) (hj : j<8) :
    si ((q6 g.val>>>(4*j))&&&7) =
      r1 g (si ((q6 0>>>(4*j))&&&7)):= by
  rw [q03 j hj];simp only [r1,s3 _ j hj]
  exact congrArg si (ym g ⟨j,hj⟩)
def u2 (permCode : Nat) : Nat->Nat->q0
  | 0,_=>rv
  | fuel+1,i =>
    if Nat.blt i 8 then si ((permCode>>>(4*i))&&&7)
    else
      let k:=i - 8
      let c:=(q2w (k>>>6)>>>(22*(k&&&63)))&&&0x3fffff
      let op:=c&&&3
      let a:=(c>>>2)&&&1023
      if Nat.beq op 0 then qx (u2 permCode fuel a)
      else
        let x:=u2 permCode fuel a
        let y:=u2 permCode fuel (c>>>12)
        if Nat.beq op 1 then (x.1&&&y.1,x.2&&&y.2) else (x.1|||y.1,x.2|||y.2)
lemma rt : ∀ (fuel i : Nat),qb (u2 (q6 0) fuel i)
  | 0,_=>vg
  | fuel+1,i=>by
    unfold u2
    split
    · exact y4 _
    · dsimp only
      split
      · exact ye (rt fuel _)
      · split
        · exact x9 false (rt fuel _) (rt fuel _)
        · exact x9 true (rt fuel _) (rt fuel _)
lemma rp (g : Fin 8) :
    ∀ (fuel i : Nat),u2 (q6 g.val) fuel i=r1 g (u2 (q6 0) fuel i)
  | 0,_=>(xw _).symm
  | fuel+1,i=>by
    unfold u2
    split
    · rename_i hi;exact xr g i (Nat.blt_eq.mp hi)
    · dsimp only
      split
      · rw [rp g fuel _];simp only [r1,us]
      · split
        · rw [rp g fuel _,rp g fuel _]
          exact (su (uu g) false _ _).symm
        · rw [rp g fuel _,rp g fuel _]
          exact (su (uu g) true _ _).symm
def r6 (permCode code j : Nat) (acc : List q0) : List q0 :=
  if code.testBit j then si ((permCode>>>(4*j))&&&7) :: acc else acc
def qq (permCode e : Nat) (acc : List q0) : List q0 :=
  if Nat.beq e 0 then acc else u2 permCode 5 (e+7) :: acc
def ur (permCode code : Nat) (acc : List q0) : List q0 :=
  r6 permCode code 0 (r6 permCode code 1 (r6 permCode code 2 (r6 permCode code 3
    (r6 permCode code 4 (r6 permCode code 5 (r6 permCode code 6 (r6 permCode code 7 acc)))))))
lemma qt (code j : Nat) {acc : List q0} (ha : ∀ x ∈ acc,qb x) :
    ∀ x ∈ r6 (q6 0) code j acc,qb x:= by
  unfold r6;split
  · intro x hx;rcases List.mem_cons.mp hx with rfl | ht;exact y4 _;exact ha x ht
  · exact ha
lemma qi (e : Nat) {acc : List q0} (ha : ∀ x ∈ acc,qb x) :
    ∀ x ∈ qq (q6 0) e acc,qb x:= by
  unfold qq;split
  · exact ha
  · intro x hx;rcases List.mem_cons.mp hx with rfl | ht;exact rt 5 _;exact ha x ht
lemma qo (g : Fin 8) (code j : Nat) (hj : j<8) (acc : List q0) :
    (r6 (q6 0) code j acc).map (r1 g) =
      r6 (q6 g.val) code j (acc.map (r1 g)):= by
  unfold r6;split <;> simp [xr g j hj]
lemma sl (g : Fin 8) (e : Nat) (acc : List q0) :
    (qq (q6 0) e acc).map (r1 g) =
      qq (q6 g.val) e (acc.map (r1 g)):= by
  unfold qq;split <;> simp [rp]
lemma ux (code : Nat) {acc : List q0} (ha : ∀ x ∈ acc,qb x) :
    ∀ x ∈ ur (q6 0) code acc,qb x:= by
  unfold ur
  exact qt _ _ (qt _ _ (qt _ _ (qt _ _
    (qt _ _ (qt _ _ (qt _ _ (qt _ _ ha)))))))
lemma uh (g : Fin 8) (code : Nat) (acc : List q0) :
    (ur (q6 0) code acc).map (r1 g) =
      ur (q6 g.val) code (acc.map (r1 g)):= by
  simp only [ur,qo g _ 0 (by omega),qo g _ 1 (by omega),
    qo g _ 2 (by omega),qo g _ 3 (by omega),
    qo g _ 4 (by omega),qo g _ 5 (by omega),
    qo g _ 6 (by omega),qo g _ 7 (by omega)]
def st (permCode k t i : Nat) : List q0 :=
  let c2:=q3y k t
  if Nat.blt i c2 then
    let code:=(q3w k t (i>>>6)>>>(28*(i&&&63)))&&&0xfffffff
    qq permCode ((code>>>8)&&&1023) (qq permCode ((code>>>18)&&&1023)
      (ur permCode code []))
  else
    let c3:=q3x k t
    if Nat.blt i c3 then
      let j:=i - c2
      let code:=(q3v k t (j>>>6)>>>(38*(j&&&63)))&&&0x3fffffffff
      qq permCode ((code>>>8)&&&1023) (qq permCode ((code>>>18)&&&1023)
        (qq permCode ((code>>>28)&&&1023) (ur permCode code [])))
    else
      let code:=(q3u k t>>>(48*(i - c3)))&&&0xffffffffffff
      qq permCode ((code>>>8)&&&1023) (qq permCode ((code>>>18)&&&1023)
        (qq permCode ((code>>>28)&&&1023) (qq permCode ((code>>>38)&&&1023)
          (ur permCode code []))))
def q8 (k t i : Nat) : List q0:=st (q6 0) k t i
lemma sx (k t i : Nat) : ∀ x ∈ q8 k t i,qb x:= by
  unfold q8 st;dsimp only
  split
  · exact qi _ (qi _ (ux _ (by simp)))
  · split
    · exact qi _ (qi _ (qi _ (ux _ (by simp))))
    · exact qi _ (qi _ (qi _ (qi _ (ux _ (by simp)))))
lemma xa (g : Fin 8) (k t i : Nat) :
    (q8 k t i).map (r1 g)=st (q6 g.val) k t i:= by
  unfold q8 st;dsimp only
  split
  · simp only [sl,uh,List.map_nil]
  · split
    · simp only [sl,uh,List.map_nil]
    · simp only [sl,uh,List.map_nil]
def r5 (k t : Nat) (w : List q0) : Bool :=
  let n:=zg k t w
  if Nat.beq n 0 then false
  else
    let m:=n - 1
    let i:=m>>>3
    Nat.blt i (qk k t) &&
      vp w (st (q6 (m&&&7)) k t i)
lemma rk {k t : Nat}
    (h : ∀ i<qk k t,qs k t (q8 k t i)) {w : List q0}
    (hw : r5 k t w=true) : qs k t w:= by
  unfold r5 at hw;dsimp only at hw
  split at hw
  · contradiction
  · simp only [Bool.and_eq_true,Nat.blt_eq] at hw
    obtain ⟨hi,hp⟩:=hw
    have hp':=yp hp
    have hlt : (zg k t w - 1)&&&7<8:= by have : (zg k t w - 1)&&&7 ≤ 7:=Nat.and_le_right;omega
    let g : Fin 8:=⟨(zg k t w - 1)&&&7,hlt⟩
    rw [← xa g k t ((zg k t w - 1)>>>3)] at hp'
    intro m hm hr
    apply h _ hi m hm
    have himg : w.toFinset.image (zk g)=(q8 k t ((zg k t w - 1)>>>3)).toFinset:= by
      ext x
      simp only [Finset.mem_image,List.mem_toFinset,hp'.mem_iff,List.mem_map]
      constructor
      · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
        have hzv:=sx k t _ z hz
        rwa [zk,r1,ut (uu g) hzv]
      · intro hx
        exact ⟨r1 g x,⟨x,hx,rfl⟩,ut (uu g) (sx k t _ x hx)⟩
    rw [← himg]
    exact xe (uu g).reverse hr
def rb (k t i : Nat) : Bool :=
  let v:=q8 k t i
  v4 v&&!xd k t v
def q4 (k t i : Nat) : Bool :=
  let v:=q8 (k+1) t i
  v4 v &&
    !v0 k t v (fun w=>!r5 k (t - 1) w) (fun w=>!r5 k t w)
def vk (t : Nat) : Bool :=
  !v0 11 t rj (fun w=>!r5 11 (t - 1) w) (fun w=>!r5 11 t w)
lemma ya {k t i : Nat} (h : rb k t i=true) :
    qs k t (q8 k t i):= by
  simp only [rb,Bool.and_eq_true,Bool.not_eq_true'] at h
  exact yy (ve h.1) h.2
lemma sk {k t i : Nat} (ht : t ≤ 5)
    (hp : ∀ t ≤ 5,∀ i<qk k t,qs k t (q8 k t i))
    (h : q4 k t i=true) : qs (k+1) t (q8 (k+1) t i):= by
  simp only [q4,Bool.and_eq_true,Bool.not_eq_true'] at h
  apply xv (ve h.1) _ _ h.2
  · intro w hw;exact rk (hp (t - 1) (by omega)) (by simpa using hw)
  · intro w hw;exact rk (hp t ht) (by simpa using hw)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3c : Theta.span (rb 8 0) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2v : Theta.span (rb 8 0) 250 250=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2u : Theta.span (rb 8 0) 250 500=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2t : Theta.span (rb 8 0) 250 750=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1q : Theta.span (rb 8 0) 250 1000=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1p : Theta.span (rb 8 0) 93 1250=true:= by decide +kernel
lemma q2r : Theta.span (rb 8 0) 1343 0=true:=(@Theta.span_join (rb 8 0) 750 0 593 (@Theta.span_join (rb 8 0) 250 0 500 q3c (@Theta.span_join (rb 8 0) 250 250 250 q2v q2u)) (@Theta.span_join (rb 8 0) 250 750 343 q2t (@Theta.span_join (rb 8 0) 250 1000 93 q1q q1p)))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3b : Theta.span (rb 8 1) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2s : Theta.span (rb 8 1) 99 250=true:= by decide +kernel
lemma q2q : Theta.span (rb 8 1) 349 0=true:=(@Theta.span_join (rb 8 1) 250 0 99 q3b q2s)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2p : Theta.span (rb 8 2) 6 0=true:= by decide +kernel
lemma q2o : Theta.span (rb 8 3) 0 0=true:=rfl
lemma q2n : Theta.span (rb 8 4) 0 0=true:=rfl
lemma q2m : Theta.span (rb 8 5) 0 0=true:=rfl
lemma q1r (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 8 t) : rb 8 t i=true:= by
  interval_cases t
  · exact Theta.span_ok q2r i (Nat.zero_le i) hi
  · exact Theta.span_ok q2q i (Nat.zero_le i) hi
  · exact Theta.span_ok q2p i (Nat.zero_le i) hi
  · exact Theta.span_ok q2o i (Nat.zero_le i) hi
  · exact Theta.span_ok q2n i (Nat.zero_le i) hi
  · exact Theta.span_ok q2m i (Nat.zero_le i) hi
lemma zt (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 8 t) : qs 8 t (q8 8 t i) :=
  ya (q1r t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q3a : Theta.span (q4 8 0) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2l : Theta.span (q4 8 0) 250 250=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2k : Theta.span (q4 8 0) 102 500=true:= by decide +kernel
lemma q2i : Theta.span (q4 8 0) 602 0=true:=(@Theta.span_join (q4 8 0) 250 0 352 q3a (@Theta.span_join (q4 8 0) 250 250 102 q2l q2k))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q39 : Theta.span (q4 8 1) 250 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2j : Theta.span (q4 8 1) 128 250=true:= by decide +kernel
lemma q2h : Theta.span (q4 8 1) 378 0=true:=(@Theta.span_join (q4 8 1) 250 0 128 q39 q2j)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q2g : Theta.span (q4 8 2) 41 0=true:= by decide +kernel
lemma q2f : Theta.span (q4 8 3) 0 0=true:=rfl
lemma q2e : Theta.span (q4 8 4) 0 0=true:=rfl
lemma q2d : Theta.span (q4 8 5) 0 0=true:=rfl
lemma q1o (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 9 t) : q4 8 t i=true:= by
  interval_cases t
  · exact Theta.span_ok q2i i (Nat.zero_le i) hi
  · exact Theta.span_ok q2h i (Nat.zero_le i) hi
  · exact Theta.span_ok q2g i (Nat.zero_le i) hi
  · exact Theta.span_ok q2f i (Nat.zero_le i) hi
  · exact Theta.span_ok q2e i (Nat.zero_le i) hi
  · exact Theta.span_ok q2d i (Nat.zero_le i) hi
lemma zr (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 9 t) : qs 9 t (q8 9 t i) :=
  sk ht zt (q1o t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q23 : Theta.span (q4 9 0) 64 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q22 : Theta.span (q4 9 1) 84 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q21 : Theta.span (q4 9 2) 43 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q20 : Theta.span (q4 9 3) 8 0=true:= by decide +kernel
lemma q1z : Theta.span (q4 9 4) 0 0=true:=rfl
lemma q1y : Theta.span (q4 9 5) 0 0=true:=rfl
lemma q0z (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 10 t) : q4 9 t i=true:= by
  interval_cases t
  · exact Theta.span_ok q23 i (Nat.zero_le i) hi
  · exact Theta.span_ok q22 i (Nat.zero_le i) hi
  · exact Theta.span_ok q21 i (Nat.zero_le i) hi
  · exact Theta.span_ok q20 i (Nat.zero_le i) hi
  · exact Theta.span_ok q1z i (Nat.zero_le i) hi
  · exact Theta.span_ok q1y i (Nat.zero_le i) hi
lemma zb (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 10 t) : qs 10 t (q8 10 t i) :=
  sk ht zr (q0z t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1x : Theta.span (q4 10 0) 5 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1w : Theta.span (q4 10 1) 6 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1v : Theta.span (q4 10 2) 6 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1u : Theta.span (q4 10 3) 6 0=true:= by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma q1t : Theta.span (q4 10 4) 1 0=true:= by decide +kernel
lemma q1s : Theta.span (q4 10 5) 0 0=true:=rfl
lemma q0y (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 11 t) : q4 10 t i=true:= by
  interval_cases t
  · exact Theta.span_ok q1x i (Nat.zero_le i) hi
  · exact Theta.span_ok q1w i (Nat.zero_le i) hi
  · exact Theta.span_ok q1v i (Nat.zero_le i) hi
  · exact Theta.span_ok q1u i (Nat.zero_le i) hi
  · exact Theta.span_ok q1t i (Nat.zero_le i) hi
  · exact Theta.span_ok q1s i (Nat.zero_le i) hi
lemma x7 (t : Nat) (ht : t ≤ 5) (i : Nat) (hi : i<qk 11 t) : qs 11 t (q8 11 t i) :=
  sk ht zb (q0y t ht i hi)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma v3 : vk 0=true/\vk 1=true/\vk 2=true/\vk 3=true/\vk 4=true/\vk 5=true:= by decide +kernel
lemma q02 (t : Nat) (ht : t ≤ 5) : vk t=true:= by
  interval_cases t
  · exact v3.1
  · exact v3.2.1
  · exact v3.2.2.1
  · exact v3.2.2.2.1
  · exact v3.2.2.2.2.1
  · exact v3.2.2.2.2.2
lemma yk (t : Nat) (ht : t ≤ 5) : qs 12 t rj:= by
  have h:=q02 t ht
  simp only [vk,Bool.not_eq_true'] at h
  apply xv q19 _ _ h
  · intro w hw;exact rk (x7 (t - 1) (by omega)) (by simpa using hw)
  · intro w hw;exact rk (x7 t ht) (by simpa using hw)
theorem no_live12 {k t : Nat} {S : Finset Sig} (hk : k ≤ 12) (h : Live k t S)
    (hsub : ∀ a ∈ S,a ∈ raw) : False:= by
  have hn : qy k t (S.image y7):=z5 h
  have hnsub : ∀ a ∈ S.image y7,a ∈ rj:= by
    intro a ha;obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp ha
    exact q00 (hsub x hx)
  have eq:=q1l hn hnsub
  rw [← eq] at hn
  have sz:=xg hn
  rw [List.toFinset_card_of_nodup q19] at sz
  have hlen : rj.length=8:=rfl
  have ht : t ≤ 5:= by omega
  exact yk t ht k hk (yl hn (xf hk))
end Base1007

end PEqualNP.Outside.L_meta_2889_aux

namespace PEqualNP.Outside.L_meta_2889_aux

lemma C6 : Base1007.one=(BitVec.allOnes 252,BitVec.allOnes 252):=rfl
lemma EW : Base1007.target=(BitVec.allOnes 252,0):=rfl
lemma DO (a : Base1007.Sig) :
    Base1007.bin false a Base1007.one=a ∧ Base1007.bin true a Base1007.zero=a ∧
    Base1007.bin false a Base1007.zero=Base1007.zero ∧ Base1007.bin true a Base1007.one=Base1007.one ∧
    Base1007.bin false a a=a ∧ Base1007.bin true a a=a:=by
  obtain ⟨p,n⟩:=a
  simp only [Base1007.bin,C6,Base1007.zero,Bool.false_eq_true,ite_true,ite_false,
    BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self]
  simp
lemma DP (d : Bool) (a b : Base1007.Sig) :
    Base1007.bin d a b=Base1007.bin d b a:=by
  cases d <;> simp [Base1007.bin,BitVec.and_comm,BitVec.or_comm]
lemma b1007_neg_laws :
    Base1007.neg Base1007.zero=Base1007.one ∧ Base1007.neg Base1007.one=Base1007.zero:=by
  simp [Base1007.neg,Base1007.zero,C6]
lemma Cf {k t S} (h : Base1007.Live k t S) : ∀ a ∈ S,Base1007.proper a:=by
  induction h using Base1007.Live.byInd with
  | stop =>
    intro a ha;rw [Finset.mem_singleton.mp ha]
    unfold Base1007.proper;rw [EW,Base1007.zero,C6];decide
  | unary ha _ _ ih=>simpa using And.intro ha (fun a h=>ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h=>ih a (Finset.mem_insert_of_mem h)⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace UnsignedBridge

open Base1007

def observe (p : Bool) (r : Fin 252) (s : Sig) : Bool :=
  (if p then s.1 else s.2).getLsbD r.val

def sample (p : Bool) (r : Fin 252) (i : Fin 8) : Bool :=
  observe p r (raw.getD i.val zero)

def graph (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)

theorem initial_observed (p : Bool) (r : Fin 252) :
    raw.map (observe p r) = List.ofFn (sample p r) := rfl

theorem zero_observed (p : Bool) (r : Fin 252) : observe p r zero = false := by
  cases p <;> simp [observe, zero]

theorem one_observed (p : Bool) (r : Fin 252) : observe p r one = true := by
  cases p <;> change (BitVec.allOnes 252).getLsbD r.val = true <;>
    rw [BitVec.getLsbD_allOnes, decide_eq_true r.isLt]

theorem target_observed (p : Bool) (r : Fin 252) : observe p r target = p := by
  cases p
  · simp [observe, target]
  · exact one_observed true r

theorem neg_observed (p : Bool) (r : Fin 252) (s : Sig) :
    observe p r (neg s) = !(observe p r s) := by
  cases p <;> simp [observe, neg, r.isLt]

theorem and_observed (p : Bool) (r : Fin 252) (a b : Sig) :
    observe p r (bin false a b) = (observe p r a && observe p r b) := by
  cases p <;> simp [observe, bin]

theorem or_observed (p : Bool) (r : Fin 252) (a b : Sig) :
    observe p r (bin true a b) = (observe p r a || observe p r b) := by
  cases p <;> simp [observe, bin]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sample_matches : ∀ (p : Bool) (r : Fin 252), graph (sample p r) = p := by
  decide +kernel

def read (ws : List Sig) (i : Nat) : Sig := ws.getD i zero

theorem read_observed (p : Bool) (r : Fin 252) (ws : List Sig) (i : Nat) :
    observe p r (read ws i) = (ws.map (observe p r)).getD i false := by
  simp only [read, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[i]? <;> simp [zero_observed]

def gateSignal (ws : List Sig) (g : Gate) : Sig :=
  let inputs := g.inputs.map (read ws)
  match g.op with
  | .and => bin false (inputs.getD 0 one) (inputs.getD 1 one)
  | .or => bin true (inputs.getD 0 zero) (inputs.getD 1 zero)
  | .not => neg (inputs.getD 0 zero)
  | _ => zero

theorem gate_observed (p : Bool) (r : Fin 252) (ws : List Sig) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    observe p r (gateSignal ws g) =
      g.op.eval (g.inputs.map fun i => (ws.map (observe p r)).getD i false) := by
  rcases g with ⟨op, inputs⟩
  have hop := hg.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have length := hg.2
  rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;>
      simp [gateSignal, GateOp.eval, and_observed, or_observed, neg_observed,
        zero_observed, one_observed]
  · rcases hop with rfl | rfl | rfl <;>
      simp [gateSignal, GateOp.eval, and_observed, or_observed, neg_observed,
        zero_observed, one_observed, read_observed]
  · rcases hop with rfl | rfl | rfl <;>
      simp [gateSignal, GateOp.eval, and_observed, or_observed, neg_observed, read_observed]
  · simp only [List.length_cons] at length
    omega

def gateInputs (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def runSignals (ws : List Sig) (gates : List Gate) : List Sig :=
  gates.foldl (fun w g => w ++ [gateSignal w g]) ws

theorem run_observed (p : Bool) (r : Fin 252) (gs : List Gate)
    (hg : ∀ g ∈ gs, gateInputs g) (ws : List Sig) :
    (runSignals ws gs).map (observe p r) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws.map (observe p r)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have g_ok := hg g (List.mem_cons_self)
    have gs_ok : ∀ a ∈ gs, gateInputs a := fun a h => hg a (List.mem_cons_of_mem _ h)
    rw [runSignals, List.foldl_cons, ← runSignals, ih gs_ok]
    simp only [List.map_append, List.map_cons, List.map_nil, List.foldl_cons, gate_observed p r ws g g_ok]

theorem read_mem_or_zero (ws : List Sig) (i : Nat) : read ws i ∈ ws.toFinset ∨ read ws i = zero := by
  simp only [read, List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => simp
  | some val => exact Or.inl (by simpa using List.mem_of_getElem? h)

end UnsignedBridge

namespace ThetaBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Base1007 UnsignedBridge

def gateNot (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

def TrackedStep (ws : Finset Sig) (z : Sig) (n : Bool) : Prop :=
  (z ∈ ws ∨ ¬ proper z) ∨
    if n then ∃ a ∈ ws, proper a ∧ z = neg a
    else ∃ d a b, a ∈ ws ∧ b ∈ ws ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

theorem direct_tracked {ws : List Sig} {a : Sig} {n : Bool}
    (h : a ∈ ws.toFinset ∨ a = zero ∨ a = one) : TrackedStep ws.toFinset a n := by
  rcases h with h | rfl | rfl
  · exact Or.inl (Or.inl h)
  · simp [TrackedStep, proper]
  · simp [TrackedStep, proper]

theorem read_tracked (ws : List Sig) (i : Nat) (n : Bool) :
    TrackedStep ws.toFinset (read ws i) n :=
  direct_tracked ((read_mem_or_zero ws i).imp_right Or.inl)

theorem negate_tracked (ws : List Sig) (i : Nat) : TrackedStep ws.toFinset (neg (read ws i)) true := by
  rcases read_mem_or_zero ws i with hm | hzero
  · by_cases ha : proper (read ws i)
    · exact Or.inr ⟨_, hm, ha, rfl⟩
    · simp only [proper, not_and_or, not_not] at ha
      rcases ha with ha0 | ha1
      · exact direct_tracked (Or.inr (Or.inr (ha0 ▸ b1007_neg_laws.1)))
      · exact direct_tracked (Or.inr (Or.inl (ha1 ▸ b1007_neg_laws.2)))
  · exact direct_tracked (Or.inr (Or.inr (hzero ▸ b1007_neg_laws.1)))

theorem binary_tracked (ws : List Sig) (d : Bool) (i j : Nat) :
    TrackedStep ws.toFinset (bin d (read ws i) (read ws j)) false := by
  let a := read ws i
  let b := read ws j
  change TrackedStep ws.toFinset (bin d a b) false
  have ma : a ∈ ws.toFinset ∨ a = zero := read_mem_or_zero ws i
  have mb : b ∈ ws.toFinset ∨ b = zero := read_mem_or_zero ws j
  by_cases ha : proper a
  · by_cases hb : proper b
    · by_cases hab : a = b
      · cases d
        · simpa [hab, (DO b).2.2.2.2.1] using read_tracked ws j false
        · simpa [hab, (DO b).2.2.2.2.2] using read_tracked ws j false
      · exact Or.inr ⟨d, a, b, ma.resolve_right ha.1, mb.resolve_right hb.1,
          ha, hb, hab, rfl⟩
    · simp only [proper, not_and_or, not_not] at hb
      rcases hb with h | h
      · cases d
        · rw [h, (DO a).2.2.1]; exact direct_tracked (Or.inr (Or.inl rfl))
        · rw [h, (DO a).2.1]; exact read_tracked ws i false
      · cases d
        · rw [h, (DO a).1]; exact read_tracked ws i false
        · rw [h, (DO a).2.2.2.1]; exact direct_tracked (Or.inr (Or.inr rfl))
  · simp only [proper, not_and_or, not_not] at ha
    rcases ha with h | h
    · cases d
      · rw [h, DP, (DO b).2.2.1]; exact direct_tracked (Or.inr (Or.inl rfl))
      · rw [h, DP, (DO b).2.1]; exact read_tracked ws j false
    · cases d
      · rw [h, DP, (DO b).1]; exact read_tracked ws j false
      · rw [h, DP, (DO b).2.2.2.1]; exact direct_tracked (Or.inr (Or.inr rfl))

theorem gate_tracked (ws : List Sig) (g : Gate) (hg : gateInputs g) :
    TrackedStep ws.toFinset (gateSignal ws g) (gateNot g) := by
  rcases g with ⟨op, inputs⟩
  have hop := hg.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  cases inputs with
  | nil =>
    have h1 (n : Bool) : TrackedStep ws.toFinset one n :=
      direct_tracked (Or.inr (Or.inr rfl))
    have h0 (n : Bool) : TrackedStep ws.toFinset zero n :=
      direct_tracked (Or.inr (Or.inl rfl))
    rcases hop with rfl | rfl | rfl
    · simpa [gateSignal, gateNot, (DO one).1] using h1 false
    · simpa [gateSignal, gateNot, (DO zero).2.1] using h0 false
    · simpa [gateSignal, gateNot, b1007_neg_laws.1] using h1 true
  | cons a inputs =>
    cases inputs with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · simpa [gateSignal, gateNot, (DO (read ws a)).1] using read_tracked ws a false
      · simpa [gateSignal, gateNot, (DO (read ws a)).2.1] using read_tracked ws a false
      · simpa [gateSignal, gateNot] using negate_tracked ws a
    | cons b rest =>
      rcases hop with rfl | rfl | rfl
      · simpa [gateSignal, gateNot] using binary_tracked ws false a b
      · simpa [gateSignal, gateNot] using binary_tracked ws true a b
      · simpa [gateSignal, gateNot] using negate_tracked ws a

theorem backwards_one {ws : Finset Sig} {z : Sig} {k t S} {n : Bool}
    (h : Live k t S) (hs : TrackedStep ws z n) (sub : S ⊆ insert z ws) :
    ∃ j u T, j ≤ k+1 ∧ (j = k+1 → u = t+n.toNat) ∧ Live j u T ∧ T ⊆ ws := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ ws
    · refine ⟨k, t, S, by omega, by omega, h, ?_⟩
      intro a ha
      rcases Finset.mem_insert.mp (sub ha) with rfl | ha'
      · exact hw
      · exact ha'
    · have hp := Cf h z hm
      let U := S.erase z
      have hU : Live k t (insert z U) := by simpa [U, Finset.insert_erase hm] using h
      have hu : U ⊆ ws := fun v hv => by
        obtain ⟨hne, hm'⟩ := Finset.mem_erase.mp hv
        exact (Finset.mem_insert.mp (sub hm')).resolve_left hne
      rcases hs with hr | hs
      · exact ((hr.resolve_left hw) hp).elim
      · cases n
        · obtain ⟨d, a, b, ha, hb, pa, pb, hab, eq⟩ := hs
          subst z
          have fresh : bin d a b ∉ insert a (insert b U) := by
            intro hr
            rcases Finset.mem_insert.mp hr with eq | hr
            · exact hw (eq.symm ▸ ha)
            rcases Finset.mem_insert.mp hr with eq | hr
            · exact hw (eq.symm ▸ hb)
            · exact hw (hu hr)
          exact ⟨_, _, _, Nat.le_refl _, by simp, Live.binary pa pb hab fresh hU,
            Finset.insert_subset_iff.mpr ⟨ha, Finset.insert_subset_iff.mpr ⟨hb, hu⟩⟩⟩
        · obtain ⟨a, ha, pa, eq⟩ := hs
          subst z
          have fresh : neg a ∉ insert a U := by
            intro hr
            rcases Finset.mem_insert.mp hr with eq | hr
            · exact hw (eq.symm ▸ ha)
            · exact hw (hu hr)
          exact ⟨_, _, _, Nat.le_refl _, by simp, Live.unary pa fresh hU,
            Finset.insert_subset_iff.mpr ⟨ha, hu⟩⟩
  · refine ⟨k, t, S, by omega, by omega, h, ?_⟩
    intro a ha
    exact (Finset.mem_insert.mp (sub ha)).resolve_left (fun eq => hm (eq ▸ ha))

theorem backwards_tracked (gs : List Gate) (hg : ∀ g ∈ gs, gateInputs g) (ws : List Sig)
    {k t : Nat} {S : Finset Sig} (h : Live k t S) (sub : S ⊆ (runSignals ws gs).toFinset) :
    ∃ j u T, j ≤ k+gs.length ∧ (j = k+gs.length → u = t+gs.countP gateNot) ∧
      Live j u T ∧ T ⊆ ws.toFinset := by
  induction gs generalizing ws with
  | nil => exact ⟨_, _, _, by simp, by simp, h, sub⟩
  | cons g gs ih =>
    have g_ok := hg g (List.mem_cons_self)
    have gs_ok : ∀ a ∈ gs, gateInputs a := fun a hh => hg a (List.mem_cons_of_mem _ hh)
    change S ⊆ (runSignals (ws ++ [gateSignal ws g]) gs).toFinset at sub
    obtain ⟨j, u, T, jbound, jc, live, ht⟩ := ih gs_ok (ws ++ [gateSignal ws g]) sub
    have sub' : T ⊆ insert (gateSignal ws g) ws.toFinset := by simpa using ht
    obtain ⟨m, v, U, mbound, mc, hl, hs⟩ := backwards_one live (gate_tracked ws g g_ok) sub'
    refine ⟨m, v, U, by simp only [List.length_cons]; omega, ?_, hl, hs⟩
    intro same
    simp only [List.length_cons] at same
    have hv := mc (by omega)
    have hu := jc (by omega)
    rw [hv, hu, List.countP_cons]
    cases h : gateNot g <;> simp [h] <;> omega

end ThetaBridge

namespace ThetaBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Base1007 UnsignedBridge

theorem circuit_live {n : Nat} (C : Circuit) (fan : FanInTwo C) (F : (Fin n → Bool) → Bool)
    (eval : ∀ x, C.eval (List.ofFn x) = F x) (initial : List Sig)
    (rows : Bool → Fin 252 → Fin n → Bool)
    (initial_ok : ∀ p r, initial.map (observe p r) = List.ofFn (rows p r))
    (rows_ok : ∀ p r, F (rows p r) = p) :
    ∃ j u T, j ≤ C.size ∧ (j = C.size → u = C.gates.countP gateNot) ∧
      Live j u T ∧ T ⊆ initial.toFinset := by
  let ws := runSignals initial C.gates
  have obs (p : Bool) (r : Fin 252) : observe p r (read ws C.output) = observe p r target := by
    rw [read_observed, run_observed p r C.gates fan, initial_ok, target_observed]
    exact (eval (rows p r)).trans (rows_ok p r)
  have output : read ws C.output = target :=
    Prod.ext (BitVec.eq_of_getLsbD_eq fun i h => obs true ⟨i, h⟩)
      (BitVec.eq_of_getLsbD_eq fun i h => obs false ⟨i, h⟩)
  have available : target ∈ ws.toFinset := by
    rcases read_mem_or_zero ws C.output with h | h
    · rwa [output] at h
    · have ne : target ≠ zero := by decide +kernel
      exact (ne (output.symm.trans h)).elim
  obtain ⟨j, u, T, bound, exact_count, live, sub⟩ :=
    backwards_tracked C.gates fan initial Live.stop (Finset.singleton_subset_iff.mpr available)
  exact ⟨j, u, T, by simpa [Circuit.size] using bound,
    by simpa [Circuit.size] using exact_count, live, sub⟩

end ThetaBridge

namespace UnsignedBridge

open PEqualNP.MetaComplexity Base1007

theorem unsignedBound : ¬ HasCircuitSize 8 graph 12 := by
  rintro ⟨C, fan, size, eval⟩
  obtain ⟨j, u, T, bound, _, live, sub⟩ :=
    ThetaBridge.circuit_live C fan graph eval raw sample initial_observed sample_matches
  exact no_live12 (bound.trans size) live (fun _ h => List.mem_toFinset.mp (sub h))

end UnsignedBridge

namespace ThetaBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Base1007 UnsignedBridge

def lowerMask : Nat := 2^232 - 1

def lower (a : Sig) : Nat :=
  ((a.1.toNat &&& lowerMask) <<< 232) ||| (a.2.toNat &&& lowerMask)

theorem lower_test (a : Sig) (j : Nat) :
    (lower a).testBit j =
      if j < 232 then a.2.toNat.testBit j else if j < 464 then a.1.toNat.testBit (j - 232) else false := by
  simp only [lower, lowerMask, Nat.testBit_or, Nat.testBit_and,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftLeft]
  by_cases hj : j < 232
  · simp [hj, show ¬ 232 ≤ j by omega]
  · by_cases hk : j < 464
    · simp [hj, hk, show 232 ≤ j by omega, show j - 232 < 232 by omega]
    · simp [hj, hk, show 232 ≤ j by omega, show ¬ j - 232 < 232 by omega]

theorem lower_target : lower target = Theta.qe := by decide +kernel

theorem neg_bit (a : BitVec 252) (i : Nat) (hi : i < 252) :
    (~~~a).toNat.testBit i = !(a.toNat.testBit i) := by
  change (~~~a).getLsbD i = !(a.getLsbD i)
  rw [BitVec.getLsbD_not]
  simp [hi]

theorem lower_neg {a : Sig} : lower (neg a) = lower a ^^^ Theta.q7 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, lower_test, lower_test, Theta.vb, Theta.zn]
  split_ifs with hl hh
  · rw [decide_eq_true (show j < 232 + 232 by omega), Bool.xor_true]
    exact neg_bit _ _ (by omega)
  · rw [decide_eq_true (show j < 232 + 232 by omega), Bool.xor_true]
    exact neg_bit _ _ (by omega)
  · rw [decide_eq_false (show ¬ j < 232 + 232 by omega)]
    rfl

theorem lower_bin (d : Bool) (a b : Sig) :
    lower (bin d a b) = if d then lower a ||| lower b else lower a &&& lower b := by
  apply Nat.eq_of_testBit_eq
  intro j
  cases d <;> simp only [bin, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_or,
    Nat.testBit_and, lower_test, BitVec.toNat_and, BitVec.toNat_or] <;> split_ifs <;> rfl

def extendSide (a : Nat) : BitVec 252 :=
  BitVec.ofNat 252 ((a &&& lowerMask) ||| (if a.testBit 0 then ((2^20 - 1) <<< 232) else 0))

def extendPair (a : Nat) : Sig := (extendSide (a >>> 232), extendSide a)

def markedRows : List Sig := Theta.xs517.map extendPair

def thetaInit : List Sig :=
  [markedRows.getD 3 zero, markedRows.getD 0 zero, markedRows.getD 2 zero,
   markedRows.getD 6 zero, markedRows.getD 4 zero, markedRows.getD 5 zero,
   markedRows.getD 1 zero]

theorem marked_rows_eq : markedRows.map lower = Theta.xs517 := by decide +kernel

theorem marked_rows_nodup : markedRows.Nodup := by decide +kernel

theorem theta_initial_set : thetaInit.toFinset = markedRows.toFinset := by decide +kernel

def thetaSample (p : Bool) (r : Fin 252) (i : Fin 7) : Bool :=
  observe p r (thetaInit.getD i.val zero)

theorem theta_initial_observed (p : Bool) (r : Fin 252) :
    thetaInit.map (observe p r) = List.ofFn (thetaSample p r) := rfl

def thetaGraph (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (x 1 && x 5) ||
    (x 2 && x 6) || (x 3 && x 5) || (x 4 && x 6) || (x 6 && x 3)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem theta_sample_matches : ∀ (p : Bool) (r : Fin 252), thetaGraph (thetaSample p r) = p := by
  decide +kernel

theorem theta_live (C : Circuit) (fan : FanInTwo C)
    (eval : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = thetaGraph x) :
    ∃ j u T, j ≤ C.size ∧ (j = C.size → u = C.gates.countP gateNot) ∧
      Live j u T ∧ T ⊆ markedRows.toFinset := by
  simpa only [theta_initial_set] using
    circuit_live C fan thetaGraph eval thetaInit thetaSample theta_initial_observed theta_sample_matches

end ThetaBridge

namespace ThetaBridge

open Base1007

def Ay (del v : List Sig) : List Sig:=v.filter (fun x=>!(del.contains x))
def BV (U : Finset Sig) (del : List Sig) : List Sig:=del.filter (fun a=>decide (a ∈ U))
lemma Cv {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset=del.toFinset ∪ U) :
    (BV U del ++ Ay del v).Nodup ∧ (BV U del ++ Ay del v).toFinset=U:=by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U:=by
    rw [← List.mem_toFinset,he];simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq;subst b
    simp [BV] at ha;simp [Ay] at hb;exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,BV,Ay,
      decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all
lemma Br (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del,x ∈ v) : v.Perm (del ++ Ay del v):=by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e;subst b;simp [Ay] at hb;exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,Ay,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all
theorem raw_marked {k t S} (h : Live k t S) (v : List Sig) (hv : v.Nodup) (he : v.toFinset = S) :
    Theta.MarkedRun neg (bin false) (bin true) target k (decide (0 < t)) v := by
  induction h using Live.byInd generalizing v with
  | stop =>
    exact Theta.MarkedRun.perm
      (List.perm_of_nodup_nodup_toFinset_eq (by simp) hv (by simp [he])) Theta.MarkedRun.done
  | @unary k t U a ha hf _ ih =>
    let rest := Ay [a] v
    have ham : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    obtain ⟨hn, eq⟩ := Cv (del := [a]) hv (by simp) (by simpa using he)
    let save := decide (a ∈ U)
    have kept : Theta.kept save a rest = BV U [a] ++ rest := by
      by_cases hm : a ∈ U <;> simp [save, Theta.kept, BV, hm]
    rw [← kept] at hn eq
    have hs : (neg a :: Theta.kept save a rest).toFinset = insert (neg a) U := by
      rw [List.toFinset_cons, eq]
    have hnd : (neg a :: Theta.kept save a rest).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hz => hf (Finset.mem_insert_of_mem ?_), hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p := (Br [a] v hv (by simp) (by simpa using ham)).symm
    simpa using Theta.MarkedRun.perm p (Theta.MarkedRun.one true save (ih _ hnd hs))
  | @binary k t U a b d _ _ hab hf _ ih =>
    let rest := Ay [a, b] v
    have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    obtain ⟨hn, eq⟩ := Cv (del := [a, b]) hv (by simp [hab]) (by simpa using he)
    let sa := decide (a ∈ U)
    let sb := decide (b ∈ U)
    have kept : Theta.kept sa a (Theta.kept sb b rest) = BV U [a, b] ++ rest := by
      by_cases ham : a ∈ U <;> by_cases hbm : b ∈ U <;> simp [sa, sb, Theta.kept, BV, ham, hbm]
    rw [← kept] at hn eq
    have hs : (bin d a b :: Theta.kept sa a (Theta.kept sb b rest)).toFinset = insert (bin d a b) U := by
      rw [List.toFinset_cons, eq]
    have hnd : (bin d a b :: Theta.kept sa a (Theta.kept sb b rest)).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hz => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)), hn⟩
      exact eq ▸ List.mem_toFinset.mpr hz
    have p := (Br [a, b] v hv (by simp [hab]) (by simp [ah, bh])).symm
    have hr := ih _ hnd hs
    cases d
    · exact Theta.MarkedRun.perm p (Theta.MarkedRun.two true sa sb hr)
    · exact Theta.MarkedRun.perm p (Theta.MarkedRun.two false sa sb hr)

theorem live_to_marked {k t S} (h : Live k t S) (v : List Sig) (hv : v.Nodup) (he : v.toFinset = S) :
    Theta.MarkedNatRun k (decide (0 < t)) (v.map lower) := by
  unfold Theta.MarkedNatRun
  rw [← lower_target]
  exact Theta.MarkedRun.map lower (fun _ => lower_neg) (fun a b => by simp [lower_bin])
    (fun a b => by simp [lower_bin]) (raw_marked h v hv he)

end ThetaBridge

namespace ThetaBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Base1007 UnsignedBridge

theorem theta_circuit_run (C : Circuit) (fan : FanInTwo C)
    (eval : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = thetaGraph x) :
    ∃ j u, j ≤ C.size ∧ (j = C.size → u = C.gates.countP gateNot) ∧
      Theta.MarkedNatRun j (decide (0 < u)) Theta.xs517 := by
  obtain ⟨j, u, T, bound, exact_count, live, sub⟩ := theta_live C fan eval
  let bank := markedRows.filter fun v => decide (v ∈ T)
  have nodup : bank.Nodup := marked_rows_nodup.filter _
  have set_eq : bank.toFinset = T := by
    ext v
    simp only [bank, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨List.mem_toFinset.mp (sub h), h⟩⟩
  have hRun := live_to_marked live bank nodup set_eq
  have sublist : (bank.map lower).Sublist Theta.xs517 := by
    rw [← marked_rows_eq]
    exact List.Sublist.map _ List.filter_sublist
  have bank_eq : bank.map lower = Theta.xs517 := by
    by_contra ne
    exact Theta.yn _ (List.mem_sublists.2 sublist) ne (Theta.vl hRun.forget)
  exact ⟨j, u, bound, exact_count, bank_eq ▸ hRun⟩

theorem theta_circuit_lower (C : Circuit) (fan : FanInTwo C)
    (eval : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = thetaGraph x) :
    11 ≤ C.size := by
  obtain ⟨j, u, bound, _, run⟩ := theta_circuit_run C fan eval
  by_contra no
  have run' := run.forget
  rw [Theta.vb, Theta.vc] at run'
  exact Theta.GG j (by omega) run'

theorem nonmonotone_theta_run (C : Circuit) (fan : FanInTwo C) (size : C.size ≤ 11)
    (eval : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = thetaGraph x)
    (has_not : ∃ g ∈ C.gates, g.op = .not) : Theta.MarkedNatRun 11 true Theta.xs517 := by
  obtain ⟨j, u, bound, exact_count, run⟩ := theta_circuit_run C fan eval
  have run' := run.forget
  rw [Theta.vb, Theta.vc] at run'
  have large : 11 ≤ j := by
    by_contra no
    exact Theta.GG j (by omega) run'
  have ht : 0 < C.gates.countP gateNot := by
    obtain ⟨g, hg, op⟩ := has_not
    exact List.countP_pos_iff.mpr ⟨g, hg, by simp [gateNot, op]⟩
  have num : u = C.gates.countP gateNot := exact_count (by omega)
  have mark : decide (0 < u) = true := decide_eq_true (num.symm ▸ ht)
  have j11 : j = 11 := by omega
  rwa [j11, mark] at run

end ThetaBridge

end PEqualNP.Outside.L_meta_2889_aux

-- Circuit simplification adapted from L-meta-2307.
namespace PEqualNP.Outside.L_meta_2889_aux.Cofactor
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Bool ⊕ Nat

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

def countOps (p : GateOp → Bool) (gs : List Gate) : Nat :=
  gs.countP fun g => p g.op

def countFixed (p : GateOp → Bool) (fixed : Nat → Bool) (gs : List Gate) : Nat :=
  gs.countP fun g => p g.op && g.inputs.any fixed

theorem simplify_count_fixed (p : GateOp → Bool) (op : GateOp) (m : Nat)
    (ins : List Stat) (b : Bool) (h : b = true → (simplify op m ins).1 = none) :
    countOps p (simplify op m ins).1.toList + (if p op && b then 1 else 0) ≤
      (if p op then 1 else 0) := by
  cases ho : (simplify op m ins).1 with
  | none => cases p op <;> cases b <;> simp [countOps, ho]
  | some g =>
    have hop : g.op = op := simplify_op op m ins g (by simp [ho])
    have hb : b = false := Bool.eq_false_iff.mpr fun hb => by rw [ho] at h; cases h hb
    simp [countOps, ho, hop, hb]

theorem elim_count_fixed (n : ℕ) (p : GateOp → Bool) (fixed : Nat → Bool) (gs : List Gate) :
    ∀ acc : List Stat × List Gate, (∀ g ∈ gs, NOk g) →
      (∀ i, fixed i = true → i < acc.1.length ∧
        ∃ b, acc.1.getD i (Sum.inl false) = Sum.inl b) →
      countOps p (elim n gs acc).2 + countFixed p fixed gs ≤
        countOps p acc.2 + countOps p gs := by
  induction gs with
  | nil => intro acc _ _; simp [elim, countOps, countFixed]
  | cons g gs ih =>
    intro acc hok hinv
    let acc' := elimStep n acc g
    let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
    let emit := (simplify g.op (n + acc.2.length) ins).1
    have hnok := hok g List.mem_cons_self
    have hnone : g.inputs.any fixed = true → emit = none := by
      intro h
      obtain ⟨i, hi, hfixed⟩ := List.any_eq_true.mp h
      obtain ⟨_, b, hb⟩ := hinv i hfixed
      apply simplify_count _ _ _ hnok.1.1
      · simpa [ins] using hnok.1.2
      · intro hop; simpa [ins] using hnok.2 hop
      · exact ⟨b, List.mem_map.mpr ⟨i, hi, hb⟩⟩
    have hcarry : ∀ i, fixed i = true → i < acc'.1.length ∧
        ∃ b, acc'.1.getD i (Sum.inl false) = Sum.inl b := by
      intro i hf
      obtain ⟨hi, b, hb⟩ := hinv i hf
      have hne : i ≠ acc.1.length := Nat.ne_of_lt hi
      refine ⟨by simp [acc', elimStep]; omega, b, ?_⟩
      exact (getD_snoc_ne _ _ _ _ hne).trans hb
    have htail := ih acc' (fun q hq => hok q (List.mem_cons_of_mem _ hq)) hcarry
    have hone := simplify_count_fixed p g.op (n + acc.2.length) ins (g.inputs.any fixed) hnone
    change countOps p (elim n gs acc').2 + countFixed p fixed (g :: gs) ≤
      countOps p acc.2 + countOps p (g :: gs)
    have hacc : countOps p acc'.2 = countOps p acc.2 + countOps p emit.toList :=
      List.countP_append
    rw [hacc] at htail
    change countOps p emit.toList + (if p g.op && g.inputs.any fixed then 1 else 0) ≤
      (if p g.op then 1 else 0) at hone
    have hcountFixed : countFixed p fixed (g :: gs) =
        countFixed p fixed gs + (if p g.op && g.inputs.any fixed then 1 else 0) := List.countP_cons
    have hcountOps : countOps p (g :: gs) =
        countOps p gs + (if p g.op then 1 else 0) := List.countP_cons
    rw [hcountFixed, hcountOps]
    omega

def initSigned (b : Bool) : List Stat :=
  Sum.inl b :: (List.ofFn (fun i : Fin 7 => Sum.inr i.val) ++ [Sum.inl (!b)])

def signedInput (b : Bool) (y : Fin 7 → Bool) : List Bool :=
  b :: (List.ofFn y ++ [!b])

theorem signed_input_eq (b : Bool) (y : Fin 7 → Bool) :
    signedInput b y = List.ofFn (Fin.cons b y) ++ [!((Fin.cons b y : Fin 8 → Bool) 0)] := by
  simp [signedInput, List.ofFn_succ]

theorem inv_initSigned (b : Bool) (y : Fin 7 → Bool) :
    Inv 7 (List.ofFn y) (signedInput b y) (initSigned b, []) := by
  refine ⟨by simp [initSigned, signedInput], ?_⟩
  intro i
  cases i with
  | zero => simp [initSigned, signedInput, Stat.Valid, Stat.val]
  | succ i =>
    change Stat.Valid (7 + ([] : List Gate).length)
        ((List.ofFn (fun i : Fin 7 => Sum.inr i.val) ++ [Sum.inl (!b)]).getD i (Sum.inl false)) ∧
      Stat.val (List.ofFn y)
        ((List.ofFn (fun i : Fin 7 => Sum.inr i.val) ++ [Sum.inl (!b)]).getD i (Sum.inl false)) =
          (List.ofFn y ++ [!b]).getD i false
    by_cases hi : i < 7
    · rw [List.getD_append _ _ _ _ (by simpa using hi),
        List.getD_append _ _ _ _ (by simpa using hi)]
      have hl : i < (List.ofFn (fun i : Fin 7 => (Sum.inr i.val : Stat))).length := by simpa using hi
      rw [List.getD_eq_getElem _ _ hl, List.getElem_ofFn]
      exact ⟨hi, rfl⟩
    · by_cases h7 : i = 7
      · subst i
        rw [getD_snoc_len _ _ _ 7 (by simp), getD_snoc_len _ _ _ 7 (by simp)]
        exact ⟨trivial, rfl⟩
      · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]
        exact ⟨trivial, rfl⟩

def fixedSign (i : Nat) : Bool := i == 0 || i == 8

theorem initSigned_fixed (b : Bool) (i : Nat) (h : fixedSign i = true) :
    i < (initSigned b).length ∧
      ∃ v, (initSigned b).getD i (Sum.inl false) = Sum.inl v := by
  have hi : i = 0 ∨ i = 8 := by simpa [fixedSign] using h
  rcases hi with rfl | rfl
  · simp [initSigned]
  · constructor
    · simp [initSigned]
    · refine ⟨!b, ?_⟩
      change (List.ofFn (fun i : Fin 7 => Sum.inr i.val) ++ [Sum.inl (!b)]).getD 7
        (Sum.inl false) = Sum.inl (!b)
      exact getD_snoc_len _ _ _ _ (by simp)

theorem restrict_signed (C : Circuit) (hC : FanInTwo C) (b : Bool)
    (hnc : ∃ y z : Fin 7 → Bool, C.eval (signedInput b y) ≠ C.eval (signedInput b z)) :
    ∃ D : Circuit, FanInTwo D ∧
      (∀ y : Fin 7 → Bool, D.eval (List.ofFn y) = C.eval (signedInput b y)) ∧
      (∀ p : GateOp → Bool, countOps p D.gates + countFixed p fixedSign (C.gates.map normGate)
        ≤ countOps p (C.gates.map normGate)) := by
  let gs := C.gates.map normGate
  let acc := elim 7 gs (initSigned b, [])
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g₀ (hC g₀ hg₀)
  have hval (y : Fin 7 → Bool) :
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
        C.eval (signedInput b y) := by
    have hv := inv_elim 7 _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_initSigned b y)
    rw [(hv.2 C.output).2]
    change (wiresFrom (C.gates.map normGate) (signedInput b y)).getD C.output false = _
    rw [wiresFrom_norm]
    rfl
  cases hout : acc.1.getD C.output (Sum.inl false) with
  | inl v =>
    obtain ⟨y, z, hne⟩ := hnc
    exact (hne (by rw [← hval y, ← hval z, hout]; rfl)).elim
  | inr o =>
    refine ⟨⟨acc.2, o⟩, elim_ok 7 gs _ (by simp), ?_, ?_⟩
    · intro y
      have hy := hval y
      rw [hout] at hy
      exact hy
    · intro p
      change countOps p acc.2 + countFixed p fixedSign gs ≤ countOps p gs
      simpa only [countOps, List.countP_nil, zero_add] using
        elim_count_fixed 7 p fixedSign gs (initSigned b, []) hnok (initSigned_fixed b)

theorem normGate_op (g : Gate) : (normGate g).op = g.op := by
  obtain ⟨op, ins⟩ := g
  cases op <;> rfl

theorem countOps_normGate (p : GateOp → Bool) (gs : List Gate) :
    countOps p (gs.map normGate) = countOps p gs := by
  simp [countOps, Function.comp_def, normGate_op]

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

theorem isNot_eq_true (op : GateOp) : isNot op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNot]

theorem not_isNot_eq_true (op : GateOp) : (!isNot op) = true ↔ op ≠ GateOp.not := by
  cases op <;> simp [isNot]

theorem retained_not {gs : List Gate} {D : Circuit}
    (hcount : ∀ p : GateOp → Bool, countOps p D.gates + countFixed p fixedSign gs ≤ countOps p gs)
    (hlen : gs.length ≤ D.gates.length + 1)
    (hforced : 0 < countFixed (fun op => !isNot op) fixedSign gs) :
    countOps isNot gs ≤ countOps isNot D.gates := by
  have hnon := hcount (fun op => !isNot op)
  have hs : gs.length = countOps isNot gs + countOps (fun op => !isNot op) gs :=
    List.length_eq_countP_add_countP (fun g : Gate => isNot g.op)
  have hd : D.gates.length = countOps isNot D.gates + countOps (fun op => !isNot op) D.gates :=
    List.length_eq_countP_add_countP (fun g : Gate => isNot g.op)
  omega

theorem alias_not_signed (pre post : List Gate) (out : Nat) (x : Fin 8 → Bool) :
    (Circuit.mk (pre ++ ⟨GateOp.not, [8]⟩ :: post) out).eval
        (List.ofFn x ++ [!x 0]) =
      (Circuit.mk (pre ++ ⟨GateOp.and, [0]⟩ :: post) out).eval
        (List.ofFn x ++ [!x 0]) := by
  let input := List.ofFn x ++ [!x 0]
  let wires := wiresFrom pre input
  have h0 : wires.getD 0 false = x 0 := by
    rw [getD_wiresFrom pre input 0 (by simp [input])]
    simp [input, List.getD_append _ _ _ _ (show 0 < (List.ofFn x).length by simp)]
  have h8 : wires.getD 8 false = !x 0 := by
    rw [getD_wiresFrom pre input 8 (by simp [input])]
    exact getD_snoc_len _ _ _ _ (by simp)
  change (wiresFrom (pre ++ ⟨GateOp.not, [8]⟩ :: post) input).getD out false =
    (wiresFrom (pre ++ ⟨GateOp.and, [0]⟩ :: post) input).getD out false
  simp only [wiresFrom_append]
  change (wiresFrom post (wires ++ [GateOp.not.eval [wires.getD 8 false]])).getD out false =
    (wiresFrom post (wires ++ [GateOp.and.eval [wires.getD 0 false]])).getD out false
  rw [h0, h8]
  simp [GateOp.eval]

theorem replace_unique_signed_not (C : Circuit) (hC : FanInTwo C)
    (hcap : countFixed (fun _ => true) fixedSign (C.gates.map normGate) ≤ 1)
    (hread : ∃ g ∈ C.gates.map normGate, g.op = GateOp.not ∧ 8 ∈ g.inputs) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ D.output = C.output ∧
      (∀ g ∈ D.gates, 8 ∉ g.inputs) ∧
      (∀ x : Fin 8 → Bool,
        D.eval (List.ofFn x ++ [!x 0]) = C.eval (List.ofFn x ++ [!x 0])) := by
  obtain ⟨g, hg, hop, h8⟩ := hread
  have hnok (g : Gate) (h : g ∈ C.gates.map normGate) : NOk g := by
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp h
    exact normGate_nok g₀ (hC g₀ hg₀)
  have hlen := (hnok g hg).2 hop
  have hinputs : g.inputs = [8] := by
    cases hins : g.inputs with
    | nil => simp [hins] at h8
    | cons i tail =>
      have he : tail = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [hins, List.length_cons] at hlen
        omega
      rw [hins, he] at h8
      have hi : 8 = i := by simpa using h8
      subst i
      simp [he]
  have heq : g = ⟨GateOp.not, [8]⟩ := by
    cases g
    simp_all
  rw [heq] at hg
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
  have hcounts : countFixed (fun _ => true) fixedSign pre +
      (countFixed (fun _ => true) fixedSign post + 1) ≤ 1 := by
    simpa [hsplit, countFixed, fixedSign] using hcap
  have hfree (l : List Gate) (hzero : countFixed (fun _ => true) fixedSign l = 0)
      (a : Gate) (ha : a ∈ l) : 8 ∉ a.inputs := by
    intro h
    have hpos : 0 < countFixed (fun _ => true) fixedSign l :=
      List.countP_pos_iff.mpr ⟨a, ha,
        Bool.and_eq_true_iff.mpr ⟨rfl, List.any_eq_true.mpr ⟨8, h, by decide⟩⟩⟩
    omega
  have hsplitLen := congrArg List.length hsplit
  simp only [List.length_map, List.length_append, List.length_cons] at hsplitLen
  let gs := pre ++ ⟨GateOp.and, [0]⟩ :: post
  refine ⟨⟨gs, C.output⟩, ?_, ?_, rfl, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hnok a (by rw [hsplit]; exact List.mem_append_left _ ha)).1
    · rcases List.mem_cons.mp ha with rfl | ha
      · simp [Ok]
      · exact (hnok a (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ha))).1
  · change gs.length = C.gates.length
    simp [gs, hsplitLen]
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hfree pre (by omega) a ha
    · rcases List.mem_cons.mp ha with rfl | ha
      · simp
      · exact hfree post (by omega) a ha
  · intro x
    change (Circuit.mk (pre ++ ⟨GateOp.and, [0]⟩ :: post) C.output).eval _ = _
    rw [← alias_not_signed]
    change (wiresFrom (pre ++ ⟨GateOp.not, [8]⟩ :: post) (List.ofFn x ++ [!x 0])).getD
      C.output false = _
    rw [← hsplit, wiresFrom_norm]
    rfl

end PEqualNP.Outside.L_meta_2889_aux.Cofactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2889_aux.Wiring

def G (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
  (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
  (x 5 && x 7) || (x 7 && x 4)

def row (b : Bool) : Fin 8 → Bool := ![b, true, false, false, false, false, false, false]

def lone : Fin 8 → Bool := ![true, false, false, false, false, false, false, false]

def signedInput (x : Fin 8 → Bool) : List Bool := List.ofFn x ++ [!(x 0)]

def readsSigned (g : Gate) : Bool := g.inputs.any (fun i => i == 0 || i == 8)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem getD_snoc (l : List Bool) (a : Bool) (i : ℕ) :
    (l ++ [a]).getD i false = if i < l.length then l.getD i false else if i = l.length then a else false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with hlt heq
  · rw [List.getElem?_append_left hlt]
  · subst i; simp
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)]
    rfl

private theorem foldKeep (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (gs.foldl step w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by unfold step; simp only [List.length_append, List.length_singleton]; omega)]
    rw [step, getD_snoc, ite_eq_left hj]

private def remap (n dead i : ℕ) : ℕ := if i < n then i else if i = n then dead else i - 1

private def mapped (n dead : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (remap n dead)⟩

private theorem readMap (xs zs : List Bool) (dead i : ℕ) (hdead : xs.length + zs.length ≤ dead) :
    (xs ++ false :: zs).getD i false = (xs ++ zs).getD (remap xs.length dead i) false := by
  by_cases hi : i < xs.length
  · simp only [remap, ite_eq_left hi]
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi]
  · by_cases he : i = xs.length
    · subst i
      simp only [remap, lt_irrefl, eq_self, ite_false, ite_true]
      rw [List.getD_append_right _ _ _ _ (by rfl), Nat.sub_self, List.getD_cons_zero,
        List.getD_eq_default _ _ (by simpa only [List.length_append] using hdead)]
    · simp only [remap, ite_eq_right hi, ite_eq_right he]
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      have hidx : i - xs.length = (i - 1 - xs.length) + 1 := by omega
      rw [hidx, List.getD_cons_succ]

private theorem remapFold (gs : List Gate) (xs zs : List Bool) (dead : ℕ)
    (hdead : xs.length + zs.length + gs.length ≤ dead) :
    ∃ rest : List Bool, rest.length = zs.length + gs.length ∧
      gs.foldl step (xs ++ false :: zs) = xs ++ false :: rest ∧
      (gs.map (mapped xs.length dead)).foldl step (xs ++ zs) = xs ++ rest := by
  induction gs generalizing zs with
  | nil => exact ⟨zs, by simp, rfl, rfl⟩
  | cons g gs ih =>
    let v : Bool := g.op.eval (g.inputs.map fun i => (xs ++ false :: zs).getD i false)
    have hmap : g.inputs.map (fun i => (xs ++ false :: zs).getD i false) =
        (mapped xs.length dead g).inputs.map (fun i => (xs ++ zs).getD i false) := by
      simp only [mapped, List.map_map]
      exact List.map_congr_left (fun i _ => readMap xs zs dead i (by simp only [List.length_cons] at hdead; omega))
    have hv : g.op.eval ((mapped xs.length dead g).inputs.map fun i => (xs ++ zs).getD i false) = v :=
      congrArg g.op.eval hmap.symm
    have hold : step (xs ++ false :: zs) g = xs ++ false :: (zs ++ [v]) := by
      simp only [step, v, List.append_assoc, List.cons_append]
    have hnew : step (xs ++ zs) (mapped xs.length dead g) = xs ++ (zs ++ [v]) := by
      change (xs ++ zs) ++ [g.op.eval ((mapped xs.length dead g).inputs.map fun i => (xs ++ zs).getD i false)] = _
      rw [hv, List.append_assoc]
    obtain ⟨rest, hlen, he1, he2⟩ := ih (zs ++ [v]) (by
      simp only [List.length_append, List.length_cons, List.length_nil] at *; omega)
    refine ⟨rest, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil] at *; omega
    · simpa only [List.foldl_cons, hold] using he1
    · simpa only [List.map_cons, List.foldl_cons, hnew] using he2

private theorem canRead (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := foldKeep gs w i hi

private theorem outputPos {C : Circuit} (he : ∀ x, C.eval (signedInput x) = G x) :
    C.output ≠ 0 := by
  intro ho
  have h := he lone
  change (C.gates.foldl step (signedInput lone)).getD C.output false = G lone at h
  rw [ho, canRead _ _ _ (by simp [signedInput])] at h
  exact (by decide : (signedInput lone).getD 0 false ≠ G lone) h

private theorem outputNeg {C : Circuit} (he : ∀ x, C.eval (signedInput x) = G x) :
    C.output ≠ 8 := by
  intro ho
  have h := he (fun _ => false)
  change (C.gates.foldl step (signedInput (fun _ => false))).getD C.output false =
    G (fun _ => false) at h
  rw [ho, canRead _ _ _ (by simp [signedInput])] at h
  exact (by decide : (signedInput (fun _ => false)).getD 8 false ≠ G (fun _ => false)) h

private theorem sameFold (outside : ℕ → Prop) (gs : List Gate)
    (hgate : ∀ g ∈ gs, ∀ u v : List Bool,
      (∀ i, outside i → u.getD i false = v.getD i false) →
      g.op.eval (g.inputs.map fun i => u.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false)) (xs ys : List Bool)
    (hlen : xs.length = ys.length)
    (hx : ∀ i, outside i → xs.getD i false = ys.getD i false) :
    ∀ i, outside i → (gs.foldl step xs).getD i false = (gs.foldl step ys).getD i false := by
  induction gs generalizing xs ys with
  | nil => exact hx
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun k hk => hgate k (List.mem_cons_of_mem _ hk))
      (step xs g) (step ys g) (by simp [step, hlen])
    intro i hi
    simp only [step, getD_snoc, hlen]
    split_ifs with hlt heq
    · exact hx i hi
    · exact hgate g List.mem_cons_self xs ys hx
    · rfl

private theorem eqGate {g : Gate} {outside : ℕ → Prop}
    (hread : ∀ i ∈ g.inputs, outside i) (u v : List Bool)
    (h : ∀ i, outside i → u.getD i false = v.getD i false) :
    g.op.eval (g.inputs.map fun i => u.getD i false) =
      g.op.eval (g.inputs.map fun i => v.getD i false) :=
  congrArg g.op.eval (List.map_congr_left fun i hi => h i (hread i hi))

theorem dropNeg {C : Circuit} (hf : FanInTwo C)
    (he : ∀ x, C.eval (signedInput x) = G x)
    (hread : ∀ g ∈ C.gates, 8 ∉ g.inputs) : HasCircuitSize 8 G C.size := by
  let dead := 8 + C.gates.length
  let D : Circuit := ⟨C.gates.map (mapped 8 dead), remap 8 dead C.output⟩
  refine ⟨D, ?_, by simp [D, Circuit.size], ?_⟩
  · intro v hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    obtain ⟨hop, hlen⟩ := hf z hz
    exact ⟨hop, by simpa only [mapped, List.length_map] using hlen⟩
  · intro x
    let xs := List.ofFn x
    have hs : xs.length = 8 := by simp [xs]
    have hb := sameFold (fun i => i ≠ 8) C.gates (fun g hg u v h =>
      eqGate (outside := fun i => i ≠ 8) (fun i hi e => hread g hg (e ▸ hi)) u v h)
      (xs ++ [false]) (signedInput x) (by simp [xs, signedInput])
      (fun i hi => by
        change (xs ++ [false]).getD i false = (xs ++ [!(x 0)]).getD i false
        simp only [getD_snoc, hs, ite_eq_right hi]) C.output (outputNeg he)
    obtain ⟨rest, hlen, hbefore, hafter⟩ := remapFold C.gates xs [] dead (by simp [hs, dead])
    have hbefore' : C.gates.foldl step (xs ++ [false]) = xs ++ false :: rest := hbefore
    have hafter' : (C.gates.map (mapped 8 dead)).foldl step xs = xs ++ rest := by
      simpa only [hs, List.append_nil] using hafter
    rw [hbefore'] at hb
    have hmap := readMap xs rest dead C.output (by simp [dead, hs, hlen])
    rw [hs] at hmap
    change ((C.gates.map (mapped 8 dead)).foldl step xs).getD (remap 8 dead C.output) false = G x
    rw [hafter', ← hmap, hb]
    exact he x

private theorem countHits {α : Type} (p : α → Bool) (s : List α)
    (hn : s.countP p ≤ 1) {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (ha' : p a = true) (hb' : p b = true) : a = b := by
  induction s with
  | nil => simp at ha
  | cons c s ih =>
    rw [List.countP_cons] at hn
    by_cases hc : p c = true
    · rw [hc, ite_eq_left rfl] at hn
      have hz : s.countP p = 0 := by omega
      have hhead (u : α) (hu : u ∈ c :: s) (hpu : p u = true) : u = c := by
        rcases List.mem_cons.mp hu with hm | hm
        · exact hm
        · have hp : 0 < s.countP p := List.countP_pos_iff.mpr ⟨u, hm, hpu⟩
          omega
      exact (hhead a ha ha').trans (hhead b hb hb').symm
    · rw [ite_eq_right hc] at hn
      have htail (u : α) (hu : u ∈ c :: s) (hpu : p u = true) : u ∈ s := by
        rcases List.mem_cons.mp hu with hm | hm
        · exfalso
          exact hc (hm ▸ hpu)
        · exact hm
      exact ih hn (htail a ha ha') (htail b hb hb')

private theorem signedMembership (g : Gate) :
    readsSigned g = true ↔ 0 ∈ g.inputs ∨ 8 ∈ g.inputs := by
  simp only [readsSigned, List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨i, hi, rfl | rfl⟩ <;> tauto
  · rintro (h | h)
    · exact ⟨0, h, Or.inl rfl⟩
    · exact ⟨8, h, Or.inr rfl⟩

private theorem pairInputs (l : List ℕ) (hh : l.length ≤ 2) (h0 : 0 ∈ l) (h8 : 8 ∈ l) :
    l = [0, 8] ∨ l = [8, 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp at h0
  · simp at h0 h8
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h8
    rcases h0 with rfl | rfl <;> rcases h8 with h8 | h8
    · omega
    · left; simp [h8]
    · right; simp [h8]
    · omega
  · simp at hh

private theorem rowInputRel (i : ℕ) (hi : i ≠ 0 ∧ i ≠ 8) :
    (signedInput (row false)).getD i false = (signedInput (row true)).getD i false := by
  by_cases h : i < 9
  · interval_cases i <;> first | rfl | omega
  · rw [List.getD_eq_default _ _ (by simp [signedInput]; omega),
      List.getD_eq_default _ _ (by simp [signedInput]; omega)]

private theorem pairConstant (g : Gate) (h0 : 0 ∈ g.inputs) (h8 : 8 ∈ g.inputs)
    (hf : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hn : g.op = GateOp.not → g.inputs.length ≤ 1) :
    g.op.eval (g.inputs.map fun i => (signedInput (row false)).getD i false) =
    g.op.eval (g.inputs.map fun i => (signedInput (row true)).getD i false) := by
  have ho : g.op = GateOp.and ∨ g.op = GateOp.or := by
    rcases (show g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not from
      by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hf.1) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have hs := hn h
      rcases pairInputs g.inputs hf.2 h0 h8 with hl | hl <;> simp [hl] at hs
  rcases pairInputs g.inputs hf.2 h0 h8 with hl | hl <;>
    rcases ho with hop | hop <;> rw [hl, hop] <;> decide

private theorem bothImpossible {C : Circuit} (hf : FanInTwo C)
    (he : ∀ x, C.eval (signedInput x) = G x)
    (hn : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (hr : C.gates.countP readsSigned ≤ 1) {g : Gate} (hg : g ∈ C.gates)
    (h0 : 0 ∈ g.inputs) (h8 : 8 ∈ g.inputs) : False := by
  let outside := fun i : ℕ => i ≠ 0 ∧ i ≠ 8
  have hgate : ∀ k ∈ C.gates,
      (∀ i ∈ k.inputs, outside i) ∨ k = g := by
    intro k hk
    by_cases h : readsSigned k = true
    · exact Or.inr (countHits _ _ hr hk hg h ((signedMembership g).2 (Or.inl h0)))
    · left
      intro i hi
      constructor
      · intro e
        exact h ((signedMembership k).2 (Or.inl (e ▸ hi)))
      · intro e
        exact h ((signedMembership k).2 (Or.inr (e ▸ hi)))
  -- The single reader of both signs has a constant output. All other gates ignore both signs.
  have sameAcross (gs : List Gate) (hgs : ∀ k ∈ gs,
      (∀ i ∈ k.inputs, outside i) ∨ k = g) (xs ys : List Bool)
      (hl : xs.length = ys.length) (hxl : 9 ≤ xs.length)
      (base : ∀ i < 9, xs.getD i false = (signedInput (row false)).getD i false)
      (base' : ∀ i < 9, ys.getD i false = (signedInput (row true)).getD i false)
      (heq : ∀ i, outside i → xs.getD i false = ys.getD i false) :
      ∀ i, outside i → (gs.foldl step xs).getD i false = (gs.foldl step ys).getD i false := by
    induction gs generalizing xs ys with
    | nil => exact heq
    | cons k ks ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun k hk => hgs k (List.mem_cons_of_mem _ hk))
        (step xs k) (step ys k) (by simp [step, hl]) (by simp [step]; omega)
      · intro i hi
        rw [step, getD_snoc, ite_eq_left (show i < xs.length by omega)]
        exact base i hi
      · intro i hi
        rw [step, getD_snoc, ite_eq_left (show i < ys.length by omega)]
        exact base' i hi
      · intro i hi
        simp only [step, getD_snoc, hl]
        split_ifs with hlt his
        · exact heq i hi
        · rcases hgs k List.mem_cons_self with hok | hkg
          · exact eqGate hok _ _ heq
          · subst k
            have hab : ∀ j ∈ g.inputs, j < 9 := by
              rcases pairInputs g.inputs (hf g hg).2 h0 h8 with hh | hh <;> simp [hh]
            rw [List.map_congr_left (fun j hj => base j (hab j hj)),
              List.map_congr_left (fun j hj => base' j (hab j hj))]
            exact pairConstant g h0 h8 (hf g hg) (hn g hg)
        · rfl
  have hall := sameAcross C.gates hgate (signedInput (row false)) (signedInput (row true))
    (by simp [signedInput]) (by simp [signedInput]) (fun _ _ => rfl) (fun _ _ => rfl)
    rowInputRel C.output ⟨outputPos he, outputNeg he⟩
  change C.eval (signedInput (row false)) = C.eval (signedInput (row true)) at hall
  rw [he, he] at hall
  exact (by decide : G (row false) ≠ G (row true)) hall

private theorem rowInputLe (i : ℕ) (hi : i ≠ 0) :
    (signedInput (row true)).getD i false = true →
      (signedInput (row false)).getD i false = true := by
  by_cases h : i < 9
  · interval_cases i <;> first | decide | omega
  · have zero : (signedInput (row true)).getD i false = false :=
      List.getD_eq_default _ _ (by simp [signedInput]; omega)
    rw [zero]
    intro hfalse
    contradiction

theorem negNeedsNot {C : Circuit} (hf : FanInTwo C)
    (he : ∀ x, C.eval (signedInput x) = G x)
    (hnop : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (hcount : C.gates.countP readsSigned ≤ 1)
    (hread : ∃ g ∈ C.gates, 8 ∈ g.inputs) :
    (∀ g ∈ C.gates, 0 ∉ g.inputs) ∧ (∃ g ∈ C.gates, g.op = GateOp.not) := by
  obtain ⟨g, hg, h8⟩ := hread
  have hpos : ∀ k ∈ C.gates, 0 ∉ k.inputs := by
    intro k hk h0
    have eq := countHits _ _ hcount hk hg ((signedMembership k).2 (Or.inl h0))
      ((signedMembership g).2 (Or.inr h8))
    subst k
    exact bothImpossible hf he hnop hcount hg h0 h8
  refine ⟨hpos, ?_⟩
  by_contra! hnot
  have hbin : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have hop := (hf g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact hop.elim Or.inl fun h => Or.inr (h.resolve_right (hnot g hg))
  have foldOnly (gs : List Gate) (hr : ∀ g ∈ gs, 0 ∉ g.inputs)
      (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (xs ys : List Bool) (hl : xs.length = ys.length)
      (rel : ∀ i, i ≠ 0 → xs.getD i false = true → ys.getD i false = true) :
      ∀ i, i ≠ 0 → (gs.foldl step xs).getD i false = true →
        (gs.foldl step ys).getD i false = true := by
    induction gs generalizing xs ys with
    | nil => exact rel
    | cons k ks ih =>
      simp only [List.foldl_cons]
      apply ih (fun g hg => hr g (List.mem_cons_of_mem _ hg))
        (fun g hg => hop g (List.mem_cons_of_mem _ hg)) (step xs k) (step ys k)
        (by simp [step, hl])
      intro i hi
      simp only [step, getD_snoc, hl]
      split_ifs with hlt his
      · exact rel i hi
      · intro hk
        rcases hop k List.mem_cons_self with ho | ho
        · simp only [ho, GateOp.eval, List.all_eq_true, id_eq] at hk ⊢
          intro b hb
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
          apply rel j (fun e => hr k List.mem_cons_self (e ▸ hj))
          exact hk _ (List.mem_map.mpr ⟨j, hj, rfl⟩)
        · simp only [ho, GateOp.eval, List.any_eq_true, id_eq] at hk ⊢
          obtain ⟨b, hb, hv⟩ := hk
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
          exact ⟨_, List.mem_map.mpr ⟨j, hj, rfl⟩,
            rel j (fun e => hr k List.mem_cons_self (e ▸ hj)) hv⟩
      · simp
  have htrue : C.eval (signedInput (row true)) = true := (he _).trans (by decide)
  have hfalse : C.eval (signedInput (row false)) = false := (he _).trans (by decide)
  have result := foldOnly C.gates hpos hbin (signedInput (row true)) (signedInput (row false))
    (by simp [signedInput]) rowInputLe C.output (outputPos he) htrue
  change C.eval (signedInput (row false)) = true at result
  rw [hfalse] at result
  contradiction

end PEqualNP.Outside.L_meta_2889_aux.Wiring

namespace PEqualNP.Outside.L_meta_2889_aux

private theorem signedBound
    (unsignedBound : ¬ HasCircuitSize 8 Wiring.G 12)
    (thetaBound : ∀ D : Circuit, FanInTwo D →
      (∀ y : Fin 7 → Bool, D.eval (List.ofFn y) = Wiring.G (Fin.cons false y)) →
      11 ≤ D.size ∧ (D.size ≤ 11 → ∀ g ∈ D.gates, g.op ≠ GateOp.not))
    (C : Circuit) (hC : FanInTwo C) (hsize : C.size ≤ 12)
    (hev : ∀ x : Fin 8 → Bool, C.eval (Wiring.signedInput x) = Wiring.G x) : False := by
  let gs := C.gates.map Cofactor.normGate
  let N : Circuit := ⟨gs, C.output⟩
  have normGates (g : Gate) (hg : g ∈ N.gates) : Cofactor.NOk g := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact Cofactor.normGate_nok a (hC a ha)
  have hN : FanInTwo N := fun g hg => (normGates g hg).1
  have hnlen : N.size = C.size := by simp [N, gs, Circuit.size]
  have hevN (x : Fin 8 → Bool) : N.eval (Wiring.signedInput x) = Wiring.G x := by
    rw [← hev x]
    change (Cofactor.wiresFrom gs (Wiring.signedInput x)).getD C.output false =
      (Cofactor.wiresFrom C.gates (Wiring.signedInput x)).getD C.output false
    rw [Cofactor.wiresFrom_norm]
  have oldCofactor (y : Fin 7 → Bool) :
      C.eval (Cofactor.signedInput false y) = Wiring.G (Fin.cons false y) := by
    rw [Cofactor.signed_input_eq]
    exact hev _
  have nonconstant : ∃ y z : Fin 7 → Bool,
      C.eval (Cofactor.signedInput false y) ≠ C.eval (Cofactor.signedInput false z) := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    rw [oldCofactor, oldCofactor]
    decide
  obtain ⟨D, hD, hevD, hc⟩ := Cofactor.restrict_signed C hC false nonconstant
  have hdeval (y : Fin 7 → Bool) :
      D.eval (List.ofFn y) = Wiring.G (Fin.cons false y) := (hevD y).trans (oldCofactor y)
  obtain ⟨dlower, noNot⟩ := thetaBound D hD hdeval
  have dlen : D.size + Cofactor.countFixed (fun _ => true) Cofactor.fixedSign gs ≤ C.size := by
    simpa [Cofactor.countOps, gs, Circuit.size] using hc (fun _ => true)
  have hcount : Cofactor.countFixed (fun _ => true) Cofactor.fixedSign gs ≤ 1 := by omega
  have hcountN : N.gates.countP Wiring.readsSigned ≤ 1 := hcount
  have hsmall (E : Circuit) (hf : FanInTwo E) (hs : E.size ≤ 12)
      (he : ∀ x, E.eval (Wiring.signedInput x) = Wiring.G x)
      (hn : ∀ g ∈ E.gates, 8 ∉ g.inputs) : False := by
    obtain ⟨F, hF, hFS, hFE⟩ := Wiring.dropNeg hf he hn
    exact unsignedBound ⟨F, hF, hFS.trans hs, hFE⟩
  by_cases readNeg : ∃ g ∈ N.gates, 8 ∈ g.inputs
  · obtain ⟨_, existsNot⟩ :=
      Wiring.negNeedsNot hN hevN (fun g hg => (normGates g hg).2) hcountN readNeg
    by_cases readerNot : ∃ g ∈ N.gates, g.op = GateOp.not ∧ 8 ∈ g.inputs
    · obtain ⟨E, hE, Esize, _, noRead, heval⟩ :=
        Cofactor.replace_unique_signed_not C hC hcount readerNot
      exact hsmall E hE (by rwa [Esize]) (fun x => (heval x).trans (hev x)) noRead
    · obtain ⟨q, hq, hread⟩ := readNeg
      have hnot : q.op ≠ GateOp.not := fun h => readerNot ⟨q, hq, h, hread⟩
      have hforced : 0 < Cofactor.countFixed (fun op => !Cofactor.isNot op) Cofactor.fixedSign gs := by
        apply List.countP_pos_iff.mpr
        exact ⟨q, hq, Bool.and_eq_true_iff.mpr ⟨(Cofactor.not_isNot_eq_true _).mpr hnot,
          List.any_eq_true.mpr ⟨8, hread, by decide⟩⟩⟩
      have hls : gs.length ≤ D.gates.length + 1 := by
        have hg : gs.length = C.size := by simp [gs, Circuit.size]
        rw [hg]
        exact Nat.le_trans hsize (Nat.succ_le_succ dlower)
      have hret : Cofactor.countOps Cofactor.isNot gs ≤ Cofactor.countOps Cofactor.isNot D.gates :=
        Cofactor.retained_not hc hls hforced
      have hnotg : 0 < Cofactor.countOps Cofactor.isNot gs := by
        obtain ⟨g, hg, h⟩ := existsNot
        exact List.countP_pos_iff.mpr ⟨g, hg, (Cofactor.isNot_eq_true _).mpr h⟩
      have hnotd : 0 < Cofactor.countOps Cofactor.isNot D.gates := hnotg.trans_le hret
      obtain ⟨g, hg, hop⟩ := List.countP_pos_iff.mp hnotd
      have hreader : 0 < Cofactor.countFixed (fun _ => true) Cofactor.fixedSign gs := by
        apply List.countP_pos_iff.mpr
        exact ⟨q, hq, Bool.and_eq_true_iff.mpr ⟨rfl, List.any_eq_true.mpr ⟨8, hread, by decide⟩⟩⟩
      have hdCap : D.size ≤ 11 := by omega
      exact noNot hdCap g hg ((Cofactor.isNot_eq_true _).mp hop)
  · have hn (g : Gate) (hg : g ∈ N.gates) : 8 ∉ g.inputs := fun h => readNeg ⟨g, hg, h⟩
    exact hsmall N hN (by rwa [hnlen]) hevN hn

end PEqualNP.Outside.L_meta_2889_aux

theorem PEqualNP.Outside.L_meta_2889 : ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 ∧ x1.size ≤ (12 : ℕ) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [!x2 (0 : Fin (8 : ℕ))]) = (x2 (0 : Fin (8 : ℕ)) && x2 (1 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (2 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (3 : Fin (8 : ℕ)) || x2 (0 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ)) || x2 (1 : Fin (8 : ℕ)) && x2 (5 : Fin (8 : ℕ)) || x2 (2 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (4 : Fin (8 : ℕ)) && x2 (6 : Fin (8 : ℕ)) || x2 (5 : Fin (8 : ℕ)) && x2 (7 : Fin (8 : ℕ)) || x2 (7 : Fin (8 : ℕ)) && x2 (4 : Fin (8 : ℕ))) := by
  rintro ⟨C, hC, hsize, heval⟩
  apply PEqualNP.Outside.L_meta_2889_aux.signedBound PEqualNP.Outside.L_meta_2889_aux.UnsignedBridge.unsignedBound _ C hC hsize heval
  intro D hD hDval
  have hcofactor : ∀ y : Fin 7 → Bool, PEqualNP.Outside.L_meta_2889_aux.Wiring.G (Fin.cons false y) =
      PEqualNP.Outside.L_meta_2889_aux.ThetaBridge.thetaGraph y := by decide +kernel
  have hTheta y := (hDval y).trans (hcofactor y)
  refine ⟨PEqualNP.Outside.L_meta_2889_aux.ThetaBridge.theta_circuit_lower D hD hTheta, ?_⟩
  intro hcap gate hgate hop
  have hrun := PEqualNP.Outside.L_meta_2889_aux.ThetaBridge.nonmonotone_theta_run D hD hcap hTheta ⟨gate, hgate, hop⟩
  exact PEqualNP.Outside.L_meta_2889_aux.Base1007.Theta.thetaNoNot11 hrun
