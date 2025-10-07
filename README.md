Theorem “Zero is unique least element”:
    a ≤ 0  ≡  a = 0
Proof:
  By cases: `a = 0`, `a = suc (pred a)`
    Completeness: By “Zero or successor of predecessor”
    Case `a = 0`:
        a ≤ 0 
      =⟨ Assumption `a = 0` ⟩
        0 ≤ 0 
      =⟨ “Reflexivity of ≤” ⟩
        true
      =⟨ “Reflexivity of =” ⟩
        0 = 0
      =⟨ Assumption `a = 0` ⟩
        a = 0 
    Case `a = suc (pred a)`:
        a ≤ 0 ≡ a = 0
      =⟨ Assumption `a = suc (pred a)`⟩ 
        suc (pred a) ≤ 0 ≡ suc (pred a) = 0
      =⟨ “Successor is not at most zero” ⟩
        false ≡ suc (pred a) = 0
      =⟨ “Zero is not successor” ⟩
        false ≡ false
      =⟨ “Identity of ≡” ⟩ 
        true

        
Theorem (3.82) (3.82c) “Transitivity of ⇒”: (p ⇒ q) ∧ (q ≡ r) ⇒ (p ⇒ r)
Proof:
    (p ⇒ q) ∧ (q ≡ r) ⇒ (p ⇒ r)
  =⟨ “Definition of ⇒” (3.59)⟩
    ¬ ((p ⇒ q) ∧ (q ≡ r)) ∨ (p ⇒ r)
  =⟨ “De Morgan”⟩
    ¬ (p ⇒ q) ∨ ¬ (q ≡ r) ∨ (p ⇒ r)
  =⟨ “Definition of ⇒”⟩
    ¬ (¬ p ∨ q) ∨ ¬ (q ≡ r) ∨ (¬ p ∨ r)
  =⟨ “De Morgan”⟩
    (¬ ¬ p ∧ ¬ q) ∨ (¬ p ∨ r) ∨ ¬ (q ≡ r) 
  =⟨ “Absorption” ⟩
    ¬ p ∨ ¬ q ∨ r ∨ ¬ (q ≡ r) 
  =⟨ “Commutativity of ¬ with ≡” ⟩
    ¬ p ∨ ¬ q ∨ r ∨ (q ≡ ¬ r)
  =⟨ “Distributivity of ∨ over ≡” ⟩
    ¬ p ∨ ¬ q ∨ (r ∨ q ≡ r ∨ ¬ r)
  =⟨ “LEM” ⟩
    ¬ p ∨ ¬ q ∨ (r ∨ q ≡ true)
  =⟨ “Identity of ≡” ⟩
    ¬ p ∨ ¬ q ∨ r ∨ q 
  =⟨ “LEM” ⟩
    ¬ p ∨ r ∨ true
  =⟨ “Zero of ∨” ⟩
    true  


Theorem (3.55): (p ∧ q) ∧ r ≡ p ≡ q ≡ r ≡ p ∨ q ≡ q ∨ r ≡ r ∨ p ≡ p ∨ q ∨ r
Proof:
    (p ∧ q) ∧ r
  ≡ ⟨ “Golden rule” ⟩ 
    (p ≡ q ≡ p ∨ q) ∧ r
  ≡ ⟨ “Golden rule” with `p, q ≔ (p ≡ q ≡ p ∨ q), r` ⟩ 
    (p ≡ q ≡ p ∨ q) ≡ r ≡ (p ≡ q ≡ p ∨ q) ∨ r
  ≡ ⟨ “Distributivity of ∨ over ≡” ⟩ 
    (p ≡ q ≡ p ∨ q) ≡ r ≡ p ∨ r ≡ q ∨ r ≡ p ∨ q ∨ r 
  ≡ ⟨ “Distributivity of ∨ over ≡” ⟩ 
    (p ≡ q ≡ p ∨ q) ≡ r ≡ p ∨ r ≡ q ∨ r ≡ p ∨ q ∨ r 




Theorem (3.82) (3.82c) “Transitivity of ⇒”: (p ⇒ q) ∧ (q ≡ r) ⇒ (p ⇒ r)
Proof:
    (p ⇒ q) ∧ (q ≡ r) ⇒ (p ⇒ r)
  =⟨ “Definition of ⇒” (3.59)⟩
    ¬ ((p ⇒ q) ∧ (q ≡ r)) ∨ (p ⇒ r)
  =⟨ “De Morgan”⟩
    ¬ (p ⇒ q) ∨ ¬ (q ≡ r) ∨ (p ⇒ r)
  =⟨ “Definition of ⇒”⟩
    ¬ (¬ p ∨ q) ∨ ¬ (q ≡ r) ∨ (¬ p ∨ r)
  =⟨ “De Morgan”⟩
    (¬ ¬ p ∧ ¬ q) ∨ (¬ p ∨ r) ∨ ¬ (q ≡ r) 
  =⟨ “Absorption” ⟩
    ¬ p ∨ ¬ q ∨ r ∨ ¬ (q ≡ r) 
  =⟨ “Commutativity of ¬ with ≡” ⟩
    ¬ p ∨ ¬ q ∨ r ∨ (q ≡ ¬ r)
  =⟨ “Distributivity of ∨ over ≡” ⟩
    ¬ p ∨ ¬ q ∨ (r ∨ q ≡ r ∨ ¬ r)
  =⟨ “LEM” ⟩
    ¬ p ∨ ¬ q ∨ (r ∨ q ≡ true)
  =⟨ “Identity of ≡” ⟩
    ¬ p ∨ ¬ q ∨ r ∨ q 
  =⟨ “LEM” ⟩
    ¬ p ∨ r ∨ true
  =⟨ “Zero of ∨” ⟩
    true  



Theorem “Associativity of ·”: (k · m) · n = k · (m · n)
Proof:
  By induction on `k : ℕ`:
    Base case `(0 · m) · n = 0 · (m · n)`:
        (0 · m) · n
      = ⟨ “Definition of · for 0” ⟩
        0 · n 
      = ⟨ “Definition of · for 0” ⟩
        0 
      = ⟨ “Definition of · for 0” ⟩
        0 · (m · n)
    Induction step `(suc k · m) · n = suc k · (m · n)`:
        (suc k · m) · n
      = ⟨ “Definition of · for `suc`” ⟩
        (m + k · m) · n
      = ⟨ “Distributivity of · over +” ⟩
        m · n + (k · m) · n
      = ⟨ Induction hypothesis ⟩
        m · n + k · (m · n)
      = ⟨ “Definition of · for `suc`” ⟩
        suc k · (m · n)


Theorem “Monus exchange”: m + (n - m) = n + (m - n)
Proof:
  By induction on `m : ℕ`:
    Base case `0 + (n - 0) = n + (0 - n)`:
        0 + (n - 0) = n + (0 - n)
      =⟨ “Right-identity of subtraction”⟩
        0 + n = n + (0 - n)
      =⟨ “Subtraction from zero”⟩
        0 + n = n + 0 — This is “Symmetry of +”
    Induction step `suc m + (n - suc m) = n + (suc m - n)`:
      By induction on `n : ℕ`:
        Base case `suc m + (0 - suc m) = 0 + (suc m - 0)`:
            suc m + (0 - suc m) = 0 + (suc m - 0)
          =⟨ “Right-identity of subtraction”⟩ 
            suc m + (0 - suc m) = 0 + suc m 
          =⟨ “Subtraction from zero” ⟩ 
            suc m + 0 = 0 + suc m — This is “Symmetry of +”
        Induction step `suc m + (suc n - suc m) = suc n + (suc m - suc n)`:
            suc m + (suc n - suc m)
          = ⟨ “Subtraction of successor from successor” ⟩ 
            suc m + (n - m)
          = ⟨ “Definition of + for `suc`”  ⟩ 
            suc (m + (n - m))
          = ⟨ Induction hypothesis `m + (n - m) = n + (m - n)` ⟩ 
            suc (n + (m - n))
          = ⟨ “Definition of + for `suc`” ⟩ 
            suc n + (m - n)
          = ⟨ “Subtraction of successor from successor” ⟩ 
            suc n + (suc m - suc n)


Theorem (3.59) “Definition of ⇒”: p ⇒ q ≡ ¬ p ∨ q
Proof:
    p ⇒ q
  =⟨ “Definition of ⇒” ⟩
    p ∨ q ≡ q
  =⟨ (3.32) ⟩
    ¬ p ∨ q


Theorem (3.60) “Definition of ⇒”: p ⇒ q ≡ p ∧ q ≡ p
Proof:
    p ⇒ q
  =⟨ “Definition of ⇒” ⟩
    p ∨ q ≡ q
  =⟨ “Golden rule” ⟩
    p ∧ q ≡ p



Theorem (3.89) “Shannon”: E[z ≔ p] ≡ (p ∧ E[z ≔ true]) ∨ (¬ p ∧ E[z ≔ false])
Proof:
    E[z ≔ p]
  =⟨ “Identity of ∧”⟩
    true ∧ E[z ≔ p] 
  =⟨ “LEM”⟩
    (p ∨ ¬ p) ∧ E[z ≔ p] 
  =⟨ “Distributivity of ∧ over ∨”⟩
    (p ∧ E[z ≔ p]) ∨ (¬ p ∧ E[z ≔ p])
  =⟨ “Replace by `true`” (3.87)⟩
    (p ∧ E[z ≔ true]) ∨ (¬ p ∧ E[z ≔ p])
  =⟨ “Definition of ¬ from ≡”⟩
    (p ∧ E[z ≔ true]) ∨ ((p ≡ false) ∧ E[z ≔ p])
  =⟨ “Replacement” (3.84a) with “Definition of ≡”⟩
    (p ∧ E[z ≔ true]) ∨ ((p ≡ false) ∧ E[z ≔ false])
  =⟨ “Definition of ¬ from ≡” ⟩
    (p ∧ E[z ≔ true]) ∨ (¬ p ∧ E[z ≔ false])





Theorem “Multiplication is not isotonic”:
    ¬ (b ≤ c  ≡  a · b ≤ a · c)[a, b, c ≔ -1 , 0 , 1 ]
Proof:
    ¬ (b ≤ c  ≡  a · b ≤ a · c)[a, b, c ≔ -1 , 0 , 1 ]
  =⟨ Substitution ⟩
    ¬ (0 ≤ 1  ≡ -1 · 0 ≤ -1 · 1)
  =⟨ Fact `0 ≤ 1` ⟩
    ¬ (true  ≡ -1 · 0 ≤ -1 · 1)
  =⟨ Fact `-1 · 0 = 0` ⟩
    ¬ (true  ≡ 0 ≤ -1 · 1)
  =⟨ Fact `-1 · 1 = -1` ⟩
    ¬ (true  ≡ 0 ≤ -1)
  =⟨ “Identity of ≡” ⟩
    ¬ (0 ≤ -1)
  =⟨ Fact `0 ≤ -1 ≡ false` ⟩
    ¬ false
  =⟨ “Negation of `false`” ⟩ 
    true


Theorem “Proof by contradiction”:  ¬ p ⇒ false  ≡  p
Proof:
    ¬ p ⇒ false
  =⟨ “Material implication” ⟩
    ¬ ¬ p ∨ false
  =⟨ “Double negation” ⟩
    p ∨ false
  =⟨ “Identity of ∨” ⟩
    p 



Calculation:
    ∀ i : ℕ ❙ 3 ≤ i < 9
            • (i - 5) · (8 - i) < 2 ∨ j = i
  = ⟨ Quantification expansion, Substitution, Evaluation⟩
       (0 · 5 < 2 ∨ j = 3) ∧ (0 · 4 < 2 ∨ j = 4)
     ∧ (0 · 3 < 2 ∨ j = 5) ∧ (1 · 2 < 2 ∨ j = 6)
     ∧ (2 · 1 < 2 ∨ j = 7) ∧ (3 · 0 < 2 ∨ j = 8)
  = ⟨ Evaluation ⟩
       (true ∨ j = 3) ∧ (true ∨ j = 4)
     ∧ (true ∨ j = 5) ∧ (false ∨ j = 6)
     ∧ (false ∨ j = 7) ∧ (true ∨ j = 8)
  = ⟨ “Zero of ∨”, “Identity of ∨” ⟩
       true ∧ true
     ∧ true ∧ (j = 6)
     ∧ (j = 7) ∧ true
  = ⟨ “Identity of ∧” ⟩
       (j = 6) ∧ (j = 7)




Theorem “Asymmetry of <”: a < b ⇒ ¬ (b < a)
Proof:
    By induction on `a : ℕ`:
      Base case `0 < b ⇒ ¬ (b < 0)`:
          0 < b ⇒ ¬ (b < 0)
        =⟨ “Nothing is less than zero”⟩
          0 < b ⇒ ¬ false
        =⟨ “Negation of `false`”⟩
          0 < b ⇒ true
        =⟨ “Right-zero of ⇒”⟩
          true
      Induction step `suc a < b ⇒ ¬ (b < suc a)`:
        By induction on `b : ℕ`:
          Base case `suc a < 0 ⇒ ¬ (0 < suc a)`:
              suc a < 0 ⇒ ¬ (0 < suc a)
            =⟨ “Nothing is less than zero” ⟩
              false ⇒ ¬ (0 < suc a)
            =⟨ “ex falso quodlibet” ⟩
              true
          Induction step `suc a < suc b ⇒ ¬ (suc b < suc a)`:
              suc a < suc b ⇒ ¬ (suc b < suc a)
            = ⟨ “<-Isotonicity of successor” ⟩
              a < b ⇒ ¬ (b < a)
            = ⟨ Induction hypothesis `a < b ⇒ ¬ (b < a)` ⟩
              true


Theorem “Non-<-monotonicity of predecessor”:
    ¬ (a < b ⇒ pred a < pred b)[a, b ≔ 0, 1]
Proof:
    ¬ (a < b ⇒ pred a < pred b)[a, b ≔ 0, 1]
  =⟨ Substitution ⟩
    ¬ (0 < 1 ⇒ pred 0 < pred 1)
  =⟨ “Predecessor” ⟩
    ¬ (0 < 1 ⇒ 0 - 1 < 1 - 1)
  =⟨ “Self-cancellation of subtraction” ⟩
    ¬ (0 < 1 ⇒ 0 - 1 < 0)
  =⟨ “Subtraction from zero” ⟩
    ¬ (0 < 1 ⇒ 0 < 0)
  =⟨ “Nothing is less than zero”  ⟩
    ¬ (0 < 1 ⇒ false)
  =⟨ Fact `1 = suc 0`  ⟩
    ¬ (0 < suc 0 ⇒ false)
  =⟨ “Zero is less than successor”  ⟩
    ¬ (true ⇒ false)
  =⟨ “Left-identity of ⇒” ⟩
    ¬ false
  =⟨ “Negation of `false`”⟩ 
    true

Theorem “<-Monotonicity of predecessor”:
    suc a < b ⇒ pred (suc a) < pred b
Proof:
  By induction on `b : ℕ`:
    Base case `suc a < 0 ⇒ pred (suc a) < pred 0`:
        suc a < 0
      =⟨ “Nothing is less than zero” ⟩
        false
      ⇒⟨ “ex falso quodlibet”⟩
        pred (suc a) < pred 0 
    Induction step `suc a < suc b ⇒ pred (suc a) < pred (suc b)`:
        suc a < suc b ⇒ pred (suc a) < pred (suc b)
      =⟨ “<-Isotonicity of successor”⟩
        a < b ⇒ pred (suc a) < pred (suc b)
      =⟨ “Predecessor of successor”⟩
        a < b ⇒ a < b — This is “Reflexivity of ⇒”


Lemma “Zero is not product of successors”:
    suc a · suc b = 0  ≡  false
Proof:
    suc a · suc b = 0
  =⟨ “Zero product” ⟩
    suc a = 0 ∨ suc b = 0
  =⟨ “Zero is not successor” ⟩
    false ∨ false
  =⟨ “Idempotency of ∨”⟩
    false 
 
Lemma “Cancellation of multiplication with successor”:
    suc c · a = suc c · b  ≡  a = b
Proof:
  By induction on `a : ℕ`:
    Base case `suc c · 0 = suc c · b  ≡  0 = b`:
        suc c · 0 = suc c · b
      ≡⟨ “Right-zero of ·” ⟩
        0 = suc c · b
      ≡⟨ “Definition of · for `suc`” ⟩
        0 = b + c · b
      ≡⟨ “Zero sum” ⟩
        0 = b ∧ 0 = c · b
      ≡⟨ Substitution ⟩
        0 = b ∧ (0 = c · z)[z ≔ b]
      ≡⟨ “Replacement” ⟩
        0 = b ∧ (0 = c · z)[z ≔ 0]
      ≡⟨ Substitution ⟩
        0 = b ∧ 0 = c · 0
      ≡⟨ “Right-zero of ·” ⟩
        0 = b ∧ true
      ≡⟨ “Identity of ∧” ⟩
        0 = b
    Induction step `suc c · suc a = suc c · b  ≡  suc a = b`:
      By induction on `b : ℕ`:
        Base case `suc c · suc a = suc c · 0  ≡  suc a = 0`:
            suc c · suc a = suc c · 0
          ≡⟨ “Right-zero of ·” ⟩
            suc c · suc a = 0
          ≡⟨ “Zero is not product of successors” ⟩
            false
          ≡⟨ “Zero is not successor” ⟩
            suc a = 0
        Induction step `suc c · suc a = suc c · suc b  ≡  suc a = suc b`:
            suc c · suc a = suc c · suc b
          ≡⟨ “Multiplying the successor” ⟩
            suc c + suc c · a = suc c + suc c · b
          ≡⟨ “Cancellation of +” ⟩
            suc c · a = suc c · b
          ≡⟨ Induction hypothesis `suc c · a = suc c · b  ≡  a = b` ⟩
            a = b
          ≡⟨ “Cancellation of `suc`” ⟩
            suc a = suc b
      
Theorem “Cancellation of ·”:
    c ≠ 0 ⇒ (c · a = c · b  ≡  a = b)
Proof:
  By cases: `c = 0`, `c = suc (pred c)`
    Completeness: By “Zero or successor of predecessor”
    Case `c = 0`:
        c ≠ 0 ⇒ (c · a = c · b  ≡  a = b)
      =⟨ Assumption `c = 0`⟩
        0 ≠ 0 ⇒ (c · a = c · b  ≡  a = b)
      =⟨ “Irreflexivity of ≠” ⟩
        false ⇒ (c · a = c · b  ≡  a = b)
      =⟨ “ex falso quodlibet” ⟩
        true
    Case `c = suc (pred c)`:
         c ≠ 0 ⇒ (c · a = c · b  ≡  a = b)
      =⟨ Assumption `c = suc (pred c)`⟩
         suc (pred c) ≠ 0 ⇒ (suc (pred c) · a = suc (pred c) · b  ≡  a = b)
      =⟨ “Zero is not successor” ⟩
         true ⇒ (suc (pred c) · a = suc (pred c) · b  ≡  a = b)
      =⟨ “Cancellation of multiplication with successor” ⟩
         true ⇒ true
      =⟨ “Reflexivity of ⇒” ⟩
         true      


 Theorem “Split <-≤-suc range at top”:
   m ≤ n ⇒ (m < i ≤ suc n  ≡  m < i ≤ n  ∨  i = suc n)
Proof:
  Assuming `m ≤ n` and using with “Definition of ≤ in terms of `suc` and <”:
      m < i ≤ suc n
    =⟨ “Reflexivity of =” ⟩
      m < i ∧ (i ≤ suc n) 
    =⟨ “Definition of ≤ in terms of <”⟩ 
      m < i ∧ (i < suc n ∨ i = suc n)
    =⟨ “Distributivity of ∧ over ∨” ⟩
      (m < i ∧ i < suc n) ∨ (m < i ∧ i = suc n)
    =⟨ Substitution ⟩  
      (m < i ∧ i < suc n) ∨ ((m < z)[z ≔ i] ∧ i = suc n)
    =⟨ Substitution ⟩  
      (m < i ∧ i < suc n) ∨ ((m < z)[z ≔ i] ∧ i = suc n)
    =⟨ “Replacement” (3.84a) , Substitution⟩
      (m < i ∧ i < suc n) ∨ (m < suc n ∧ i = suc n) 
    =⟨ Assumption `m ≤ n` , “Identity of ∧”⟩
      (m < i ∧ i < suc n) ∨ i = suc n
    =⟨ “Definition of ≤ in terms of `suc` and <” ⟩
      (m < i ∧ i ≤ n) ∨ i = suc n
    =⟨ “Reflexivity of =” ⟩
      m < i ≤ n ∨ i = suc n

Lemma “Subproof”: pos a ⇒ (pos (a · b) ⇒ pos b)
Proof:
  Assuming `pos a`:
    By cases: `pos b`, `¬ pos b`
      Completeness: By “Excluded middle”
      Case `pos b`:
          pos (a · b) ⇒ pos b
        =⟨ Assumption `pos b` ⟩ 
          pos (a · b) ⇒ true
        =⟨ “Right-zero of ⇒” ⟩ 
          true
      Case `¬ pos b`:
        By cases: `b = 0`, `b ≠ 0`
          Completeness:
              (b = 0) ∨ (b ≠ 0)
            =⟨ “Definition of ≠” ⟩
              (b = 0) ∨ ¬ (b = 0)
            =⟨ “LEM”⟩
              true
          Case `b = 0`:
              pos (a · b) ⇒ pos b
            =⟨ Assumption `b = 0`, “Zero of ·”, “Non-positivity of 0” ⟩
              false ⇒ pos b
            =⟨ “ex falso quodlibet”⟩
              true 
          Case `b ≠ 0`:
            Side proof for `a · b ≠ 0`:
                a · b ≠ 0
              ⇐⟨ “Shunting”, “Non-zero multiplication” ⟩
                a ≠ 0 ∧ b ≠ 0
              ≡⟨ “Identity of ∧” , Assumption `b ≠ 0` ⟩
                a ≠ 0
              ⇐⟨ “Positive implies non-zero” ⟩
                pos a   — This is Assumption `pos a`
            Continuing with goal `pos (a · b) ⇒ pos b`:
                pos (a · b) ⇒ pos b
              =⟨ “Contrapositive” ⟩
                ¬ pos b ⇒ ¬ pos (a · b)
              =⟨ “Positivity under unary minus” (15.33b) with Assumption `b ≠ 0` ⟩  
                pos (- b) ⇒ ¬ pos (a · b)
              =⟨ “Positivity under unary minus” (15.33b) with local property `a · b ≠ 0`⟩ 
                pos (- b) ⇒ pos (- (a · b))
              =⟨ (15.20) ⟩ 
                pos (- b) ⇒ pos (a · (- b))
              =⟨ “Identity of ∧” , Assumption `pos a` ⟩ 
                pos a ∧ pos (- b) ⇒ pos (a · (- b))
              =⟨ “Positivity under ·” ⟩ 
                true



Theorem (15.35) “Positivity under positive ·”: pos a ⇒ (pos b ≡ pos (a · b))
Proof:
  Assuming `pos a`:
      pos b ≡ pos (a · b)
    =⟨ “Mutual implication” ⟩
      (pos b ⇒ pos (a · b)) ∧ (pos (a · b) ⇒ pos b)
    =⟨ “Identity of ∧” , Assumption `pos a` ⟩
      (pos b ∧ pos a ⇒ pos (a · b)) ∧ (pos (a · b) ⇒ pos b)
    =⟨ “Positivity under ·” , “Identity of ∧”⟩
      pos (a · b) ⇒ pos b
    =⟨ “Subproof” with Assumption `pos a` ⟩ 
      true



Theorem (15.35) “Positivity under positive ·”:
  pos a ⇒ (pos b ≡ pos (a · b))
Proof:
  Assuming `pos a`:
    Using “Mutual implication”:
      Subproof for `pos b ⇒ pos (a · b)`:
          pos b ⇒ pos (a · b)
        ⇐⟨  “Positivity under ·” with “Shunting” ⟩
          pos a      — This is Assumption `pos a`
      Subproof for `pos (a · b) ⇒ pos b`:
        Using “Contrapositive”:
          Subproof for `¬ pos b ⇒ ¬ pos (a · b)`:
            By cases: `b = 0`, `b ≠ 0`
              Completeness: By “Definition of ≠”, “LEM”
              Case `b = 0`:
                  ¬ pos b ⇒ ¬ pos (a · b)
                ≡⟨ Assumption `b = 0` , “Zero of ·” ⟩
                  ¬ pos 0 ⇒ ¬ pos 0  — This is “Reflexivity of ⇒”
              Case `b ≠ 0`:
                Side proof for `a · b ≠ 0`:
                    a · b ≠ 0
                  ⇐⟨ “Shunting”, “Non-zero multiplication” ⟩
                    a ≠ 0 ∧ b ≠ 0
                  ≡⟨ “Identity of ∧”, Assumption `b ≠ 0` ⟩
                    a ≠ 0
                  ⇐⟨ “Positive implies non-zero” ⟩
                    pos a   — This is Assumption `pos a`
                Continuing with goal `¬ pos b ⇒ ¬ pos (a · b)`:
                    ¬ pos b
                  ≡⟨ “Positivity under unary minus” with Assumption `b ≠ 0` ⟩
                    pos (- b)
                  ≡⟨ “Identity of ∧”, Assumption `pos a` ⟩
                    pos a ∧ pos (- b)
                  ⇒⟨ “Positivity under ·” ⟩
                    pos (a · - b)
                  ≡⟨ (15.20) ⟩
                    pos (- (a · b))
                  ≡⟨ “Positivity under unary minus” with local property `a · b ≠ 0` ⟩
                    ¬ pos (a · b)

Theorem (15.44A) “Trichotomy — A”:
    a < b  ≡  a = b  ≡  a > b
Proof:
  Using “Mutual implication”:
    Subproof for `a = b ⇒ (a < b ≡ a > b)`:
      Assuming `a = b`:
          a < b
        ≡⟨ “Converse of <”, Assumption `a = b` ⟩
          a > b
    Subproof for `(a < b ≡ a > b) ⇒ a = b`:
        a < b ≡ a > b
      ≡⟨ “Definition of <”, “Definition of >” ⟩
        pos (b - a) ≡ pos (a - b)
      ≡⟨ (15.17), (15.19), “Subtraction” ⟩
        pos (b - a) ≡ pos (- (b - a))
      ⇒⟨ (15.33c) ⟩
        b - a = 0
      ≡⟨ “Cancellation of +” ⟩
        b - a + a = 0 + a
      ≡⟨ “Identity of +”, “Subtraction”, “Unary minus” ⟩
        a = b
  
Theorem (15.44B) “Trichotomy — B”:
    ¬ (a < b  ∧  a = b  ∧  a > b)
Proof:
    ¬ (a < b  ∧  a = b  ∧  a > b)
  =⟨ “De Morgan” ⟩
    ¬ (a < b ∧ a > b) ∨ ¬ (a = b)
  =⟨ “Converse of <”, “Asymmetry of <” ⟩
    true ∨ ¬ (a = b)
  =⟨ “Zero of ∨” ⟩
    true 
     
Theorem (15.44) “Trichotomy”:
    (a < b  ≡  a = b  ≡  a > b) ∧
    ¬ (a < b  ∧  a = b  ∧  a > b)
Proof:
    By “Idempotency of ∧”, “Trichotomy — A”, “Trichotomy — B”



Theorem: (∃ y : ℕ • ∀ x : ℕ • x + y = 7 · x) ≡ false
Proof:
  With (3.15) and “Generalised De Morgan”:
    Subproof for `∀ y : ℕ • ∃ x : ℕ • ¬ (x + y = 7 · x)`:
        For any `y : ℕ`:
            ∃ x : ℕ • ¬ (x + y = 7 · x)
          ⇐⟨ “∃-Introduction” ⟩
            (¬ (x + y = 7 · x))[x ≔ y + 1]
          =⟨ Substitution ⟩
             ¬ (y + 1 + y = 7 · (y + 1))
          =⟨ “Distributivity of · over +”, Evaluation ⟩
             ¬ (y + 1 + y = 7 · y + 6 + 1)
          =⟨ “Cancellation of +” ⟩    
             ¬ (y + y = 7 · y + 6)
          =⟨ Fact `2 + 5 = 7`, “Multiplying by 2” ⟩
             ¬ (2 · y = (2 + 5) · y + 6) 
          =⟨ “Distributivity of · over +” , “Identity of +”, “Cancellation of +” ⟩
             ¬ (0 =  5 · y + 6)
          =⟨ Fact `6 = suc 5`, “Definition of + for `suc`” ⟩
             ¬ (0 = suc (5 · y + 5))
          =⟨ “Zero is not successor” , “Negation of `false`” ⟩
              true  

Theorem: ∀ x : ℕ • ∃ y : ℕ • x + 2 · x = y · x
Proof:
  For any `x : ℕ`:
      ∃ y : ℕ • x + 2 · x = y · x
    ⇐⟨ “∃-Introduction” ⟩
      (x + 2 · x = y · x)[y ≔ 3]
    =⟨ Substitution ⟩
       x + 2 · x = 3 · x
    =⟨ “Multiplying by 2” ⟩
       x + x + x = 3 · x — This is “Multiplying by 3”  
       
Theorem: ∃ y : ℕ • ∀ x : ℕ • x + 2 · x = y · x
Proof:
      ∃ y : ℕ • ∀ x : ℕ • x + 2 · x = y · x
    ⇐⟨ “∃-Introduction” ⟩
      (∀ x : ℕ • x + 2 · x = y · x)[y ≔ 3]
    =⟨ Substitution ⟩
       ∀ x : ℕ • x + 2 · x = 3 · x
  Proof for this:
    For any `x : ℕ`:
        x + 2 · x = 3 · x
      =⟨ “Multiplying by 2” ⟩
        x + x + x = 3 · x — This is “Multiplying by 3”  


Theorem “M1.3.3”:
   ∃ k : ℤ • ∃ n : ℤ • 3 · k + 7 · n = 32
Proof:
  ∃ k : ℤ • ∃ n : ℤ • 3 · k + 7 · n = 32
⇐⟨“∃-Introduction”⟩
  (∃ n : ℤ • 3 · k + 7 · n = 32)[k ≔ 6]
≡⟨Substitution⟩
  (∃ n : ℤ • 3 · 6 + 7 · n = 32)
⇐⟨“∃-Introduction”⟩
  (3 · 6 + 7 · n = 32) [n ≔ 2]
≡⟨Substitution⟩
  3 · 6 + 7 · 2 = 32
≡⟨Fact `3 · 6 = 18`⟩
  18 + 7 · 2 = 32
≡⟨Fact `2 · 7 = 14`⟩
  18 + 14 = 32
≡⟨Fact `18 + 14 = 32`⟩
  32 = 32
≡⟨“Reflexivity of =”⟩
  true

  
1:  Theorem “M1.3.4”:
 2:        x = f k ∧ y = f (k + 1)
 3:      ⇒⁅ x := y ⍮ k := k + 1 ⍮ y := f (k + 1) ⁆
 4:        x = f k ∧ y = f (k + 1)
 5:  Proof:
 6:      x = f k ∧ y = f (k + 1)
 7:    ≡⟨?⟩
 8:      x = f (k + 1) ∧ f (k + 1 ) = f (k + 1)
 9:    ≡⟨“Cancellation of +”⟩
10:      x = f (k + 1) ∧ f (k + 1 + 1) = f (k + 1 + 1)
11:    ⇒⁅ k := k + 1 ⁆ ⟨ “Assignment” with substitution ⟩
12:      x = f k ∧ f (k + 1) = f (k + 1)
13:    ⇒⁅ y := f (k + 1) ⁆ ⟨ “Assignment” with substitution ⟩
14:      x = f k ∧ y = f (k + 1)



Theorem “Split off term” “Split off term at top”:
    (∏ i : ℕ ❙ i < suc n • E) = (∏ i : ℕ ❙ i < n • E) · E[i ≔ n]
Proof:
        (∏ i ❙ i < suc n • E)
    =⟨ “Zero is least element”, “Identity of ∧” ⟩
        (∏ i ❙ 0 ≤ i < suc n • E)
    =⟨ Subproof for `0 ≤ i < suc n ≡ 0 ≤ i < n  ∨  i = n`:
            By “Split range at top” with “Zero is least element”
      ⟩
        (∏ i ❙ 0 ≤ i < n  ∨  i = n • E)
    =⟨ “Zero is least element” , “Identity of ∧” ⟩
        (∏ i ❙ i < n  ∨  i = n • E)
    =⟨ “Disjoint range split for ∏”
        with subproof for `∀ i • i < n  ∧  i = n  ≡ false`:
            For any `i`:
                 i < n  ∧  i = n
              ≡⟨ Substitution ⟩
                 (z < n)[z ≔ i]  ∧  i = n
              ≡⟨ “Replacement” (3.84a) , Substitution ⟩
                 n < n  ∧  i = n
              ≡⟨ “Irreflexivity of <”, “Zero of ∧” ⟩
                 false
      ⟩
        (∏ i ❙ i < n • E) · (∏ i ❙ i = n • E)
    =⟨ “One-point rule for ∏” ⟩
        (∏ i ❙ i < n • E) · E[i ≔ n]

Theorem “Split off term” “Split off term at top”:
    m ≤ n ⇒
    (∏ i ❙ m ≤ i < suc n • E) = (∏ i ❙ m ≤ i < n • E) · E[i ≔ n]
Proof:
  Assuming `m ≤ n`:
        (∏ i ❙ m ≤ i < suc n • E)
    =⟨ “Split range at top” with Assumption `m ≤ n` ⟩
        (∏ i ❙ m ≤ i < n  ∨  i = n • E)
    =⟨ “Disjoint range split for ∏”
       with subproof for `∀ i • m ≤ i < n  ∧  i = n  ≡ false`:
           For any `i`:
                m ≤ i < n  ∧  i = n
             ≡⟨ Substitution ⟩
                (m ≤ z < n)[z ≔ i]  ∧  i = n
             ≡⟨ “Replacement” (3.84a) , Substitution ⟩
                m ≤ n < n  ∧  i = n
             ≡⟨ “Irreflexivity of <”, “Zero of ∧” ⟩
                false
      ⟩
        (∏ i ❙ m ≤ i < n • E) · (∏ i ❙ i = n • E)
    =⟨ “One-point rule for ∏” ⟩
        (∏ i ❙ m ≤ i < n • E) · E[i ≔ n]

Theorem “Split off term at top using ≤”:
    (∏ i ❙ i ≤ suc n • E) = (∏ i ❙ i ≤ n • E) · E[i ≔ suc n]
Proof:
    (∏ i ❙ i ≤ suc n • E)
  =⟨ “Definition of ≤ in terms of <” ⟩ 
    (∏ i ❙ i < suc n ∨ i = suc n • E)
  =⟨ “Disjoint range split for ∏”  
      with subproof for `∀ i • i < suc n ∧ i = suc n ≡ false`:
        For any `i : ℕ`:
            i < suc n ∧ i = suc n
          =⟨ Substitution ⟩
            (z < suc n)[z ≔ i] ∧ i = suc n
          =⟨ “Replacement” (3.84a), Substitution ⟩
            suc n < suc n ∧ i = suc n
          =⟨ “Irreflexivity of <” , “Zero of ∧” ⟩
            false   
    ⟩ 
    (∏ i ❙ i < suc n • E) · (∏ i ❙ i = suc n • E)
  =⟨ “Definition of ≤ in terms of `suc` and <” 
    , “One-point rule for ∏” ⟩
     (∏ i ❙ i ≤ n • E) · E[i ≔ suc n]

