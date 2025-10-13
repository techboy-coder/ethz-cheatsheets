#import "@preview/showybox:2.0.4": showybox

#let homepage = link("https://cs.shivi.io")[cs.shivi.io]
#let author = "Shivram Sambhus (Group K, HS25)"
#let title = "DM Cheatsheet - Logic & Proofs"

#set page(
  paper: "a4",
  flipped: true,
  margin: (x: 10pt, y: 10pt),
  footer: context [
    #grid(
      columns: 1fr,
      align: (right),
      gutter: 0pt,
      [
        #counter(page).display("1 / 1", both: true)
      ],
    )
  ],
)


#set text(size: 8pt)

#set heading(numbering: "1.1")

#let color-box = (
  rgb("#268bd2"), // Blue
  rgb("#859900"), // Green
  rgb("#b58900"), // Yellow
  rgb("#cb4b16"), // Orange
  rgb("#d33682"), // Magenta
  rgb("#6c71c4"), // Violet
)

#show heading: it => {
  let index = counter(heading).at(it.location()).first()
  let hue = color-box.at(calc.rem(index - 1, color-box.len()))

  let color = hue.darken(30% * (it.depth - 1))

  let heading_size = 7.5pt
  let inset_size = 1.0mm


  set text(white, size: heading_size)
  set align(left)
  block(
    radius: 0.6mm,
    inset: inset_size,
    width: 100%,
    above: 7.5pt,
    below: 7.5pt,
    fill: color,
    it,
  )
}

#let concept-block(
  body: content,
  alignment: start,
  width: 100%,
  fill-color: white,
) = context {
  let heading-count = counter(heading).at(here()).first()
  let current-color = color-box.at(calc.rem(heading-count - 1, color-box.len()))
  block(
    breakable: true,
    stroke: 1pt + current-color,
    fill: fill-color,
    radius: 3pt,
    inset: 6pt,
    width: width,
  )[
    #align(alignment)[
      #body
    ]
  ]
}

#let inline(title) = context {
  let heading-count = counter(heading).at(here()).first()
  let current-color = color-box.at(calc.rem(heading-count - 1, color-box.len()))

  box(grid(
    columns: (1fr, auto, 1fr),
    align: horizon + center,
    column-gutter: 1em,
    line(length: 100%, stroke: 1pt + current-color),
    text(fill: current-color, weight: "bold")[#title],
    line(length: 100%, stroke: 1pt + current-color),
  ))
}

#columns(3, gutter: 6pt)[

  #text(title, weight: "bold") - #text(author)

  = Introduction: The Structure of Mathematical Reasoning
  _This document provides a structured overview of the core tools for formal reasoning in discrete mathematics: propositional logic, predicate logic, and standard proof techniques. The goal is to present a clear, procedural approach to constructing and analyzing mathematical arguments._

  == TOC

  #outline(title: none)

  = Part I: Propositional Logic (Aussagenlogik)
  _Propositional logic is the foundation of mathematical reasoning. It deals with propositions (statements that are either true or false) and the logical connectives that combine them._
  
  == Propositions and Connectives
  #concept-block(body: [
    #inline[Core Concepts]
    A *proposition* is a declarative sentence with a definite truth value (True/1 or False/0).
    #table(
      columns: 3,
      align: center,
      table.header([*Connective*], [*Symbol*], [*Meaning*]),
      [Negation], [$not P$], ["it is not the case that P],
      [Conjunction], [$P and Q$], ["P and Q are both true],
      [Disjunction], [$P or Q$], ["at least one of P or Q is true],
      [Implication], [$P -> Q$], ["if P is true, then Q is true],
      [Biconditional], [$P <-> Q$], ["P and Q have the same truth value],
    )
  ])

  == Truth Tables and Logical Status
  #concept-block(body: [
    #inline[Procedure: Constructing a Truth Table]
    1.  Create a column for each atomic proposition ($n$ variables).
    2.  Create $2^n$ rows to list all possible combinations of truth values.
    3.  Add columns for complex sub-formulas, building up from simplest to most complex.
    4.  Fill each new column by applying the definition of its main connective to its constituent columns.

    #inline[Example: Truth Table for $(P or Q) -> (P and Q)$]
    #table(
      columns: 5,
      align: center,
      table.header([$P$], [$Q$], [$P or Q$], [$P and Q$], [$(P or Q) -> (P and Q)$]),
      [0], [0], [0], [0], [1],
      [0], [1], [1], [0], [0],
      [1], [0], [1], [0], [0],
      [1], [1], [1], [1], [1],
    )

    #inline[Definitions of Logical Status]
    - *Tautology:* A formula that is always true (final column is all 1s). E.g., $P or not P$.
    - *Contradiction:* A formula that is always false (final column is all 0s). E.g., $P and not P$.
    - *Contingency:* A formula that is neither a tautology nor a contradiction.
    - *Satisfiable:* A formula that is true for at least one assignment of truth values (i.e., not a contradiction).
  ])

  == Logical Equivalences
  #concept-block(body: [
    #inline[Concept]
    Two formulas $F$ and $G$ are *logically equivalent* ($F equiv G$) if they have identical truth tables. This means $F equiv G$ is a tautology. Equivalences are the rules for algebraic manipulation of logical formulas.

    #inline[Fundamental Laws]
    - *De Morgan's Laws:*
      $not(P and Q) equiv (not P or not Q)$
      $not(P or Q) equiv (not P and not Q)$
    - *Distributive Laws:*
      $P and (Q or R) equiv (P and Q) or (P and R)$
      $P or (Q and R) equiv (P or Q) and (P or R)$
    - *Implication Equivalence:*
      $P -> Q equiv not P or Q$
    - *Contrapositive:*
      $P -> Q equiv not Q -> not P$
    - *Biconditional Equivalence:*
      $P equiv Q equiv (P -> Q) and (Q -> P)$
    - *Double Negation:* $not(not P) equiv P$

    #box(fill: luma(240), inset: 4pt, radius: 2pt)[
      
      *TA Tip: The Implication Pitfall*

      The expression $P -> Q$ is only false when a true premise leads to a false conclusion ($T -> F$). If the premise $P$ is false, the implication is *vacuously true*. This is a common source of confusion but is essential for mathematical reasoning.
    ]
  ])

  = Part II: Predicate Logic (Prädikatenlogik)
  _Predicate logic extends propositional logic by introducing variables, predicates, and quantifiers, allowing for statements about properties of objects and relationships between them._

  == Predicates and Quantifiers
  #concept-block(body: [
    - *Universe of Discourse ($UU$):* The non-empty set of objects that variables can represent (e.g., integers, people, all cats).
    - *Predicate:* A property that becomes a proposition when its variables are assigned values from the UoD. E.g., $P(x) = "x > 3"$.
    - *Universal Quantifier ($forall$):* "For all". $forall x, P(x)$ is true if $P(x)$ is true for every $x$ in the UoD.
    - *Existential Quantifier ($exists$):* "There exists". $exists x, P(x)$ is true if there is at least one $x$ in the UoD for which $P(x)$ is true.
  ])

  == Nested Quantifiers
  #concept-block(body: [
    #inline[Procedure for Interpretation]
    1.  Read from left to right. The order is critical.
    2.  The choice for a variable bound by an inner quantifier can depend on the variables of the outer quantifiers.
    3.  Think of it as a nested loop or a challenge-response game: $forall x$ means "for any $x$ an opponent gives you...", $exists y$ means "...you can find a $y$ such that...".

    #inline[Simple Example]
    UoD = Integers.
    - $forall x exists y, x < y$: "For every integer, there is a larger integer." (True, choose $y=x+1$).
    - $exists y forall x, x < y$: "There exists an integer that is larger than all integers." (False, no maximum integer exists).

    #inline[Harder Example]
    UoD = People. $L(x,y) = x "loves" y$.
    - $forall x exists y, L(x,y)$: "Everybody loves somebody." (The person loved can be different for each individual).
    - $exists y forall x, L(x,y)$: "There is somebody who is loved by everybody." (A single, universally loved person exists).
  ])

  == Negating Quantified Statements
  #concept-block(body: [
    #inline[Procedure (De Morgan's for Quantifiers)]
    1.  Place a $not$ in front of the entire quantified statement.
    2.  "Push" the $not$ inward across each quantifier one by one.
    3.  Each time the $not$ passes a quantifier, the quantifier flips ($forall$ becomes $exists$, and vice versa).
    4.  Once inside, apply standard propositional De Morgan's laws to the predicate expression.

    #inline[Simple Example]
    $not(forall x P(x)) equiv exists x not P(x)$

    $not(exists x P(x)) equiv forall x not P(x)$

    #inline[Harder Example]
    
    *Statement:* "All students who studied passed the exam."
    $forall x ((S(x) and T(x)) -> P(x))$
    
    *Negation Procedure:*
    1.  $not(forall x ((S(x) and T(x)) -> P(x)))$
    2.  $equiv exists x not((S(x) and T(x)) -> P(x))$ (Flip $forall$, push $not$ in)
    3.  $equiv exists x not(not(S(x) and T(x)) or P(x)))$ (Implication law)
    4.  $equiv exists x (S(x) and T(x)) and not P(x))$ (De Morgan's & Double Negation)
    
    *Meaning:* "There exists someone who is a student, studied, and did not pass."
  ])

  == Translating Natural Language
  #concept-block(body: [
    #inline[Procedure for Translation]
    1.  Define the Universe of Discourse ($UU$).
    2.  Define predicates for each property (e.g., $C(x)$ for "$x$ is a cat").
    3.  Identify the main logical structure ($forall$, $exists$, $->$, $and$).
    4.  Translate piece by piece, adhering to the standard patterns.

    #inline[Standard Patterns]
    - "All A's are B's": $forall x (A(x) -> B(x))$
    - "Some A's are B's": $exists x (A(x) and B(x))$
    - "No A's are B's": $forall x (A(x) -> not B(x))$
    - "Not all A's are B's": $exists x (A(x) and not B(x))$

    #box(fill: luma(240), inset: 4pt, radius: 2pt)[
      
      *The Golden Rule of Translation:*
      - Use $->$ as the main connective with $forall$.
      - Use $and$ as the main connective with $exists$.
      
      *Why?*
      - $forall x (A(x) and B(x))$ means "Everything in the universe is both an A and a B". This is almost always too strong.
      - $exists x (A(x) -> B(x))$ means "There exists something that, if it's an A, is also a B". This is true if there's just one thing in the UoD that is *not* an A, making it too weak and usually not what is intended.
    ]
  ])

  = Part III: Proof Techniques (Beweismuster)
  _This section outlines the fundamental strategies for constructing mathematical proofs. A systematic approach involves identifying the claim's structure and selecting the most appropriate technique._

  == Direct Proof (Direkter Beweis)
  #concept-block(body: [
    #inline[Procedure]
    To prove an implication $P -> Q$:
    1.  Assume $P$ is true.
    2.  Use definitions, axioms, and established theorems to build a logical chain of deductions.
    3.  Conclude that $Q$ must be true.

    #inline[Simple Example]
    
    *Claim:* If $n$ is an odd integer, then $n^2$ is odd.
    
    *Proof:* Assume $n$ is odd. By definition, $n = 2k + 1$ for some integer $k$. Then $n^2 = (2k+1)^2 = 4k^2 + 4k + 1 = 2(2k^2 + 2k) + 1$. Let $m = 2k^2 + 2k$. Since $k$ is an integer, $m$ is an integer. Thus, $n^2 = 2m + 1$, which is the definition of an odd number.
  ])

  == Proof by Contraposition (Kontraposition)
  #concept-block(body: [
    #inline[Procedure]
    To prove $P -> Q$, instead prove its logically equivalent contrapositive, $not Q -> not P$. This is often simpler when the conclusion $Q$ is a negative statement.
    1.  Assume $not Q$ is true.
    2.  Follow logical steps to show that $not P$ must be true.

    #inline[Simple Example]
    
    *Claim:* For an integer $n$, if $n^2$ is even, then $n$ is even.
    
    *Proof:* The contrapositive is "If $n$ is not even (odd), then $n^2$ is not even (odd)." This is precisely the statement proven in the Direct Proof example above. Since the contrapositive is true, the original statement is true.
  ])

  == Proof by Contradiction (Widerspruchsbeweis)
  #concept-block(body: [
    #inline[Procedure]
    To prove a statement $P$:
    1.  Assume $not P$ is true.
    2.  From this assumption, derive a logical contradiction (a statement of the form $R and not R$).
    3.  Conclude that the assumption $not P$ must be false, hence $P$ is true.

    #inline[Harder Example: Infinitude of Primes]
    
    *Claim:* There are infinitely many prime numbers.
    
    *Proof:*
    1.  Assume for contradiction that there is a finite number of primes. Let them be $p_1, p_2, ..., p_n$.
    2.  Consider the number $N = (p_1 times p_2 times ... times p_n) + 1$.
    3.  $N$ must have a prime factor. Let this prime factor be $p$.
    4.  This prime $p$ must be one of the primes in our list, so $p = p_i$ for some $i$.
    5.  This means $p_i$ divides $N$. But $p_i$ also divides the product $p_1 times ... times p_n$.
    6.  If $p_i$ divides both numbers, it must divide their difference: $N - (p_1 times ... times p_n) = 1$.
    7.  *Contradiction:* No prime number can divide 1.
    8.  Therefore, the assumption of a finite number of primes is false.
  ])

  == Proof by Cases (Fallunterscheidung)
  #concept-block(body: [
    #inline[Procedure]
    1.  Partition the problem domain into a set of exhaustive cases $C_1, C_2, ..., C_k$.
    2.  Prove the statement for each case individually.
    3.  Since the cases cover all possibilities, the statement holds universally.

    #inline[Simple Example]
    
    *Claim:* For any integer $n$, $n^2 >= n$.
    
    *Proof:*
    - *Case 1: $n >= 1$.* Multiplying both sides of $n >= 1$ by the positive number $n$ gives $n^2 >= n$.
    - *Case 2: $n = 0$.* $0^2 >= 0$ becomes $0 >= 0$, which is true.
    - *Case 3: $n < 0$.* Here, $n^2$ is non-negative, while $n$ is negative. Any non-negative number is greater than any negative number, so $n^2 > n$.
    Since the statement holds in all three exhaustive cases, it is true for all integers.
  ])

  == Proof by Induction (Vollständige Induktion)
  #concept-block(body: [
    #inline[Procedure (Weak Induction)]
    To prove $forall n >= n_0, P(n)$:
    1.  *Base Case (Induktionsanfang):* Verify $P(n_0)$ is true.
    2.  *Inductive Hypothesis (Annahme):* Assume $P(k)$ is true for an arbitrary $k >= n_0$.
    3.  *Inductive Step (Schritt):* Using the hypothesis, prove that $P(k+1)$ is also true.

    #inline[Simple Example (Weak)]
    
    *Claim:* $sum_(i=1)^n i = n(n+1)/2$ for $n >= 1$.
    
    *Proof:*
    - *Base Case (n=1):* $sum_(i=1)^1 i = 1$. And $1(1+1)/2 = 1$. True.
    - *Hypothesis:* Assume $sum_(i=1)^k i = k(k+1)/2$.
    - *Step:* Show for $k+1$:
      $sum_(i=1)^(k+1) i = (sum_(i=1)^k i) + (k+1)$
      $ = k(k+1)/2 + (k+1) $ (by hypothesis)
      $ = (k+1)(k/2 + 1) = (k+1)(k+2)/2$. This is the required formula for $n=k+1$.

    #inline[Procedure (Strong Induction)]
    _Strong induction assumes truth for all prior cases up to k, while weak assumes only for k._

    1.  *Base Case(s):* Verify $P(n_0)$ (and possibly more initial cases).
    2.  *Hypothesis:* Assume $P(j)$ is true for *all* integers $j$ where $n_0 <= j <= k$.
    3.  *Step:* Using the hypothesis, prove $P(k+1)$ is true.

    #inline[Harder Example (Strong)]
    
    *Claim:* Any postage of $n >= 12$ cents can be made with 4- and 5-cent stamps.

    *Proof:*
    - *Base Cases:*
      $P(12): 3 times 4$. True.
      $P(13): 2 times 4 + 1 times 5$. True.
      $P(14): 1 times 4 + 2 times 5$. True.
      $P(15): 3 times 5$. True.
    - *Hypothesis:* Assume for an arbitrary $k >= 15$, $P(j)$ is true for all $j$ with $12 <= j <= k$.
    - *Step:* We want to show $P(k+1)$. Consider the postage for $k-3$. Since $k >= 15$, $k-3 >= 12$. By our strong hypothesis, we know we can make postage for $k-3$. To get postage for $k+1$, we simply add a 4-cent stamp: $(k-3)+4 = k+1$. Thus, $P(k+1)$ is true.
  ])
]