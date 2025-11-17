#import "@preview/showybox:2.0.4": showybox

#let homepage = link("https://cs.shivi.io")[cs.shivi.io]
#let author = "Shivram Sambhus (Group K, HS25)"
#let title = "DM Cheatsheet - Sets, Relations, & Functions"

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

  = Introduction: The Building Blocks of Discrete Structures
  _This document covers the fundamental concepts of sets, relations, and functions as presented in Chapter 3._

  == TOC

  #outline(title: none)

  = Part I: Sets (Mengenlehre)
  _A set is an unordered collection of distinct objects. This is the most fundamental structure in mathematics._

  == Core Concepts & Notation
  #concept-block(body: [
    - *Element of:* $x in A$ ("x is an element of set A").
    - *Set-Builder Notation:* ${ x in U | P(x) }$ ("the set of all x in universe U such that property P(x) is true").
    - *Empty Set:* $emptyset$ or ${}$ (the unique set with no elements).
    - *Cardinality:* $|A|$ (the number of elements in a finite set A).
    - *Power Set:* $cal(P)(A)$ (the set of all subsets of A). If $|A|=n$, then $|cal(P)(A)| = 2^n$.
    - *Russell's Paradox:* The "set of all sets that do not contain themselves", $R = {A | A in.not A}$, leads to a contradiction ($R in R <=> R in.not R$). This paradox revealed that not every property can define a set. We must start from an existing set, e.g. ${x in B | P(x)}$, not ${x | P(x)}$.
  ])

  == Proving Set Equality & Subsets
  #concept-block(body: [
    #inline[Core Definitions (Axiom of Extensionality)]
    - *Subset:* $A subset.eq B equiv forall x (x in A -> x in B)$.
    - *Set Equality:* $A = B equiv forall x (x in A <-> x in B) equiv (A subset.eq B) and (B subset.eq A)$.

    #box(fill: luma(235), inset: 5pt, radius: 3pt)[
      *TA Tip: The Element-Chasing Method*
      This is the standard, rigorous way to prove set relations.
      1. *To prove $A subset.eq B$*:
        - Start with "Let $x$ be an arbitrary element of $A$."
        - Use the definition of $A$ to state properties of $x$.
        - Logically deduce that $x$ must also satisfy the properties of $B$ (using definitions, logic rules).
        - Conclude with "Therefore, $x in B$."
      2. *To prove $A = B$*:
        - First, prove $A subset.eq B$.
        - Then, prove $B subset.eq A$.
        - Conclude that since both inclusions hold, by definition of equality, $A = B$.
    ]

    #inline[Example: Proving a Distributive Law]
    *Claim:* $A inter (B union C) = (A inter B) union (A inter C)$.

    *Proof:* We prove this by double inclusion.

    *Part 1: Show $A inter (B union C) subset.eq (A inter B) union (A inter C)$*

    Let $x in A inter (B union C)$.
    + $=> x in A$ and $x in (B union C)$ (Def. of Intersection)
    + $=> x in A$ and ($x in B$ or $x in C$) (Def. of Union)
    + $=> (x in A$ and $x in B$) or ($x in A$ and $x in C$) (Distributive Law of Logic)
    + $=> x in (A inter B)$ or $x in (A inter C)$ (Def. of Intersection)
    + $=> x in (A inter B) union (A inter C)$ (Def. of Union)

    *Part 2: Show $(A inter B) union (A inter C) subset.eq A inter (B union C)$*
    
    Let $x in (A inter B) union (A inter C)$.
    + $=> x in (A inter B)$ or $x in (A inter C)$ (Def. of Union)
    + $=> (x in A$ and $x in B$) or ($x in A$ and $x in C$) (Def. of Intersection)
    + $=> x in A$ and ($x in B$ or $x in C$) (Factoring out $x in A$ in logic)
    + $=> x in A$ and $x in (B union C)$ (Def. of Union)
    + $=> x in A inter (B union C)$ (Def. of Intersection)
    Since both inclusions hold, the sets are equal by definition.
  ])

  == Set Operations & Properties
  #concept-block(body: [
    #inline[Core Operations]
    - *Union:* $A union B = {x | x in A or x in B}$
    - *Intersection:* $A inter B = {x | x in A and x in B}$
    - *Difference:* $A backslash B = {x | x in A and x in.not B}$
    - *Cartesian Product:* $A times B = {(a, b) | a in A and b in B}$. Creates *ordered pairs*. Note that $A times B != B times A$ unless $A=B$ or one is empty. The product is not associative: $(A times B) times C != A times (B times C)$.

    #inline[Laws of Set Algebra]
    These are direct consequences of the laws of logic.
    - *Commutative:* $A union B = B union A$, $A inter B = B inter A$
    - *Associative:* $(A union B) union C = A union (B union C)$
    - *Distributive:* $A inter (B union C) = (A inter B) union (A inter C)$
    - *De Morgan's Laws:*
      - $overline(A union B) = overline(A) inter overline(B)$
      - $overline(A inter B) = overline(A) union overline(B)$
  ])

  = Part II: Relations (Relationen)
  _A relation describes a relationship between elements of sets. Formally, a binary relation $R$ from a set $A$ to a set $B$ is any subset of the Cartesian product $A times B$. We write $a R b$ to mean $(a,b) in R$._

  == Operations on Relations
  #concept-block(body: [
    #inline[Key Operations]
    - *Inverse ($R^(-1)$):* If $R subset.eq A times B$, then $R^(-1) subset.eq B times A$.
      $R^(-1) = {(b, a) | (a, b) in R}$.
    - *Composition ($S circle.small R$):* If $R subset.eq A times B$ and $S subset.eq B times C$.
      $S circle.small R = {(a, c) | exists b in B, (a, b) in R and (b, c) in S}$.
      *Intuition:* A path from $a$ to $c$ through some intermediate $b$. The order is critical: $S circle.small R$ means apply $R$ *then* $S$. It is associative: $(T circle.small S) circle.small R = T circle.small (S circle.small R)$.
    - *Transitive Closure ($R^+$):* $R^+ = union_(i=1)^infinity R^i = R union R^2 union R^3 union ...$
      *Intuition:* $(a,b) in R^+$ if there is a path of *any* length ($>=1$) from $a$ to $b$.
  ])

  == Properties of Relations on a Set A
  #concept-block(body: [
    #table(
      columns: 3,
      align: (left, center, left),
      table.header([*Property*], [*Definition ($forall a,b,c in A$)*], [*Intuition/Graph*]),
      [Reflexive], [$a R a$], [Every node has a self-loop.],
      [Irreflexive], [$a in.not R a$], [No node has a self-loop.],
      [Symmetric], [$a R b -> b R a$], [If there's an edge from a to b, there's one back (all edges are two-way).],
      [Antisymmetric], [$(a R b and b R a) -> a = b$], [No two distinct nodes have edges in both directions between them.],
      [Transitive], [$(a R b and b R c) -> a R c$], [If there's a path $a -> b -> c$, there's a direct edge $a -> c$. "Shortcut property".],
    )
    *Note:* Antisymmetric is *not* the negation of symmetric. A relation can be both (e.g., equality) or neither.
  ])

  == Special Types of Relations
  #concept-block(body: [
    #inline[Equivalence Relation]
    A relation that is *Reflexive, Symmetric, and Transitive*.
    - *Intuition:* Generalizes "equality". It groups similar elements together.
    - *Equivalence Class:* $[a]_R = {x in A | x R a}$. The set of all elements equivalent to $a$.
    - *Partition:* The set of all equivalence classes of a set $A$ forms a *partition* of $A$. This means the classes are non-empty, disjoint ($[a]_R inter [b]_R = emptyset$ if not $a R b$), and their union is $A$.

    #inline[Partial Order]
    A relation $R$ that is *Reflexive, Antisymmetric, and Transitive*.
    - *Intuition:* Generalizes $<=$. It defines a hierarchy where some elements may be *incomparable*.
    - *Poset:* A pair $(A, R)$ where $R$ is a partial order on $A$.
    - *Comparable vs Incomparable*: Two elements $a,b$ are comparable if $a R b$ or $b R a$. Otherwise they are incomparable.
    - *Total Order:* A partial order where every pair of elements is comparable.
    - *Hasse Diagram:* A simplified graph for a finite poset.
      1. Draw nodes for elements.
      2. If $b$ *covers* $a$ (i.e., $a prec b$ and no $c$ is between them, $a prec c prec b$), draw a line from $a$ to $b$, with $b$ placed higher.
      3. Omit self-loops (implied by reflexivity) and transitive edges (implied by transitivity). All edges point "up".
  ])

  == Elements in Posets
  #concept-block(body: [
    Let $(A, <=)$ be a poset and $S subset.eq A$.
    #inline[Minimal & Maximal Elements]
    - $a in A$ is *minimal* if no element is smaller: $not exists b in A, b < a$.
    - $a in A$ is *maximal* if no element is larger: $not exists b in A, a < b$.
    *Note:* There can be many minimal/maximal elements. In a Hasse diagram, these are the "bottom" and "top" elements.
    
    #inline[Least & Greatest Elements]
    - $a in A$ is *least* if it's smaller than or equal to all other elements: $forall b in A, a <= b$.
    - $a in A$ is *greatest* if it's greater than or equal to all other elements: $forall b in A, b <= a$.
    *Note:* If they exist, they are unique. A least element is the unique minimal element. A greatest element is the unique maximal element.
    
    #inline[Bounds for a Subset S]
    - *Lower Bound:* $a in A$ is a lower bound of $S$ if $forall s in S, a <= s$.
    - *Upper Bound:* $a in A$ is an upper bound of $S$ if $forall s in S, s <= a$.
    - *Greatest Lower Bound (infimum/meet):* glb(S) or $inf(S)$ is the greatest of all lower bounds.
    - *Least Upper Bound (supremum/join):* lub(S) or $sup(S)$ is the least of all upper bounds.

    #inline[Lattices]
    A poset $(A, <=)$ is a *lattice* if every pair of elements ${a,b}$ in $A$ has a unique meet (glb) and a unique join (lub).
  ])

  = Part III: Functions (Funktionen)
  _A function is a special type of relation that maps each element of a domain to exactly one element of a codomain._

  == Definition & Types
  #concept-block(body: [
    #inline[Formal Definition]
    A relation $f subset.eq A times B$ is a function $f: A -> B$ if it satisfies two conditions:
    1. *Totally Defined:* $forall a in A, exists b in B$ such that $(a,b) in f$. (Every element in the domain is mapped).
    2. *Well-Defined:* If $(a,b) in f$ and $(a,c) in f$, then $b=c$. (Each element is mapped to only one output).
    - *Image (Range):* $f(S) = {f(a) | a in S}$ for a subset $S subset.eq A$. The image of the function is $Im(f)=f(A)$.
    - *Preimage:* $f^(-1)(T) = {a in A | f(a) in T}$ for a subset $T subset.eq B$.

    #inline[Key Function Types]
    #table(
      columns: 3,
      align: left,
      table.header([*Type*], [*Formal Definition*], [*Intuition & Cardinality*]),
      [Injective (one-to-one)], [$forall a_1, a_2 in A, f(a_1) = f(a_2) -> a_1 = a_2$.], [No two inputs map to the same output. For finite sets, $|A| <= |B|$.],
      [Surjective (onto)], [$forall b in B, exists a in A, f(a) = b$.], [Every element in the codomain is "hit". For finite sets, $|A| >= |B|$.],
      [Bijective], [Both injective and surjective.], [A perfect one-to-one correspondence. For finite sets, $|A| = |B|$. An inverse function $f^(-1)$ exists iff $f$ is bijective.],
    )
  ])

  = Part IV: Cardinality & Countability
  _Cardinality provides a way to compare the sizes of sets, including infinite ones, using functions._

  == Comparing Set Sizes
  #concept-block(body: [
    #inline[Fundamental Definitions]
    - *Equinumerous ($A ~ B$):* $|A| = |B|$. There exists a *bijection* $f: A -> B$.
    - *Dominates ($A <= B$):* $|A| <= |B|$. There exists an *injection* $f: A -> B$.
    - *Strictly Dominates ($A < B$):* $|A| < |B|$. There is an injection from A to B, but no bijection.

    #inline[Schröder-Bernstein Theorem]
    If $|A| <= |B|$ and $|B| <= |A|$, then $|A| = |B|$.
    *Approach:* If you can find an injection from $A$ to $B$ and another injection from $B$ to $A$, you can conclude a bijection exists without actually constructing it.
  ])

  == Countable & Uncountable Sets
  #concept-block(body: [
    #inline[Definitions]
    - *Countable:* A set $A$ is countable if it is finite or countably infinite. Formally, $|A| <= |NN|$.
    - *Countably Infinite:* A set $A$ is countably infinite if $|A| = |NN|$. These are sets whose elements can be listed in an infinite sequence (e.g., $a_0, a_1, a_2, ...$).
    - *Uncountable:* A set that is not countable. Its elements cannot be put into an infinite list.

    #inline[Key Results & Proof Techniques]
    - *Countable Sets:* $NN, ZZ, QQ, NN times NN$, the set of all finite-length strings.
      *Proof Strategy:* To show a set $A$ is countable, find an *injection* from $A$ into a known countable set (like $NN$ or $NN times NN$). Example: $QQ$ is countable because any rational can be written as $p/q$, mapping to an ordered pair $(p,q) in ZZ times NN$.
    - *Uncountable Sets:* $RR, cal(P)(NN)$, the set of infinite binary sequences ${0,1}^infinity$, the interval $[0,1]$.
      *Proof Strategy:* Use Cantor's Diagonalization Argument.

    #box(fill: luma(235), inset: 5pt, radius: 3pt)[
      *Approach: Cantor's Diagonalization Argument*
      *Goal:* To prove that a set (e.g., infinite binary sequences, ${0,1}^infinity$) is uncountable.
      *Procedure:*
      1. *Assume for contradiction* that the set *is* countable. This implies we can create a complete, infinite list of all its elements.
         $s_0 = b_(0,0) b_(0,1) b_(0,2) ...$
         $s_1 = b_(1,0) b_(1,1) b_(1,2) ...$
         $s_2 = b_(2,0) b_(2,1) b_(2,2) ...$
         $dots.v$
      2. *Construct a "diagonal" enemy:* Create a new sequence, $s_("new")$, that is guaranteed *not* to be on the list. This is done by making its $n$-th element different from the $n$-th element of the $n$-th sequence in the list.
         The $n$-th bit of $s_("new")$ is the *flipped* bit of the $n$-th bit of $s_n$.
         $s_("new")_n = 1 - b_(n,n)$
      3. *Find the contradiction:* The new sequence $s_("new")$ cannot be in our list. Why?
        - It's not $s_0$ because it differs in the 0-th bit.
        - It's not $s_1$ because it differs in the 1st bit.
        - In general, it cannot be $s_n$ for any $n$ because it differs in the $n$-th bit by construction.
      4. *Conclusion:* Our list, which was assumed to be complete, is missing an element. This is a contradiction. Therefore, the initial assumption must be false, and the set is uncountable.
    ]
  ])
]